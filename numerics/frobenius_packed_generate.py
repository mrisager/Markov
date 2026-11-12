#!/usr/bin/env python3
"""Generate bounded Markov-tree residues using exact arithmetic and small buffers.

Each record is the largest coordinate modulo 2**128, stored as sixteen
little-endian bytes (low 64-bit word, then high 64-bit word). This module
does not check uniqueness: all files must subsequently be compared globally,
including the coordinator's prefix nodes and exceptional triples.

generate_job() writes one disjoint subtree. initialize_worker(configuration)
and count_job({"id": ..., "root": ...}) provide spawn-Pool integration. Only
the exact upper bound is prepared, not a table of all powers of ten.

Checkpoints are trusted local pickle files. A checkpoint is written only
after its raw records have been flushed and fsynced. On resume, any raw tail
beyond the committed checkpoint is truncated before traversal continues.
"""

from __future__ import annotations

from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import json
import math
import os
from pathlib import Path
import pickle
import re
import tempfile
import time


SCHEMA_VERSION = 1
RECORD_BYTES = 16
RESIDUE_BITS = 128
WORKER_CONFIGURATION: dict = {}


@lru_cache(maxsize=1)
def prepare_bound(max_exponent: int, backend: str):
    if not isinstance(max_exponent, int) or max_exponent < 1:
        raise ValueError("max_exponent must be a positive integer")
    if backend not in ("auto", "python", "gmpy2"):
        raise ValueError("backend must be auto, python, or gmpy2")
    integer, backend_name, version = int, "python", None
    if backend != "python":
        try:
            import gmpy2
        except ImportError:
            if backend == "gmpy2":
                raise ValueError("gmpy2 is not installed")
        else:
            integer, backend_name, version = gmpy2.mpz, "gmpy2", gmpy2.version()
    bound = integer(10) ** max_exponent
    return integer, backend_name, version, bound, bound.bit_length(), integer((1 << RESIDUE_BITS) - 1)


def job_paths(workdir: Path, job_id: str) -> dict[str, Path]:
    if not isinstance(job_id, str) or re.fullmatch(r"[A-Za-z0-9_-]{1,120}", job_id) is None:
        raise ValueError("job_id must be a short alphanumeric, hyphen or underscore identifier")
    directory = Path(workdir).resolve()
    return {
        "raw": directory / f"{job_id}.bin",
        "partial": directory / f"{job_id}.partial",
        "checkpoint": directory / f"{job_id}.checkpoint.pkl",
        "metadata": directory / f"{job_id}.metadata.json",
    }


def atomic_write(path: Path, value, *, binary: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        options = {"mode": "wb" if binary else "w", "dir": path.parent,
                   "prefix": f".{path.name}.", "delete": False}
        if not binary:
            options["encoding"] = "utf-8"
        with tempfile.NamedTemporaryFile(**options) as handle:
            temporary = Path(handle.name)
            if binary:
                pickle.dump(value, handle, protocol=pickle.HIGHEST_PROTOCOL)
            else:
                json.dump(value, handle, indent=2)
                handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def validate_identity(value: dict, identity: dict, *, expected_format: str) -> None:
    if not isinstance(value, dict) or value.get("format") != expected_format:
        raise ValueError("unexpected packed generation file format")
    for key, expected in identity.items():
        if value.get(key) != expected:
            raise ValueError(f"packed job {identity['job_id']} differs in {key}")


def validate_completed(metadata: dict, identity: dict, raw_path: Path) -> None:
    validate_identity(metadata, identity, expected_format="frobenius-packed-job-metadata")
    stats = metadata["statistics"]
    records = metadata["records"]
    if (not metadata["completed"] or not isinstance(records, int) or records < 1 or
            metadata["size_bytes"] != records * RECORD_BYTES or
            metadata["raw_path"] != str(raw_path) or not raw_path.is_file() or
            raw_path.stat().st_size != metadata["size_bytes"] or
            stats["strict_triples"] != records or stats["pruned_children"] != records + 1 or
            re.fullmatch(r"[0-9a-f]{64}", metadata["sha256"]) is None):
        raise ValueError(f"inconsistent completed packed job {identity['job_id']}")


def generate_job(max_exponent: int, root: tuple, job_id: str, configuration_id: str,
                 workdir: Path, *, backend: str = "gmpy2", buffer_records: int = 1_000_000,
                 checkpoint_seconds: float = 300, progress_every: int = 5_000_000,
                 resume: bool = False, stop_after: int | None = None) -> dict:
    """Return completed metadata, or completed=False for a controlled partial run.

    Identical completed jobs are reused after validating identity and file
    length. Their SHA-256 should be verified by the global sorter while it
    reads the records. Unfinished jobs require resume=True; checkpoints fix
    both the exact DFS frontier and the durable raw-record prefix.
    """
    started = time.perf_counter()
    if not isinstance(configuration_id, str) or not configuration_id:
        raise ValueError("configuration_id must be non-empty")
    if not isinstance(buffer_records, int) or buffer_records < 1:
        raise ValueError("buffer_records must be positive")
    if not isinstance(progress_every, int) or progress_every < 0:
        raise ValueError("progress_every must be non-negative")
    if not math.isfinite(checkpoint_seconds) or checkpoint_seconds <= 0:
        raise ValueError("checkpoint_seconds must be positive and finite")
    if stop_after is not None and (not isinstance(stop_after, int) or stop_after < 1):
        raise ValueError("stop_after must be a positive absolute generated-record count")
    integer, backend_name, backend_version, bound, bound_bits, mask = prepare_bound(max_exponent, backend)
    initial_root = tuple(map(int, root))
    if len(initial_root) != 3:
        raise ValueError("root must have three coordinates")
    a, b, c = initial_root
    if not (0 < a < b < c <= bound) or a*a + b*b + c*c != 3*a*b*c:
        raise ValueError("root must be a strict Markov triple below the bound")
    paths = job_paths(Path(workdir), job_id)
    paths["raw"].parent.mkdir(parents=True, exist_ok=True)
    identity = {
        "schema_version": SCHEMA_VERSION, "configuration_id": configuration_id,
        "job_id": job_id, "max_exponent": max_exponent,
        "initial_root": list(initial_root), "backend": backend_name,
        "record_bytes": RECORD_BYTES, "residue_bits": RESIDUE_BITS,
        "byte_order": "little",
    }
    if paths["metadata"].exists():
        metadata = json.loads(paths["metadata"].read_text(encoding="utf-8"))
        validate_completed(metadata, identity, paths["raw"])
        return metadata
    state = None
    if paths["checkpoint"].exists():
        if not resume:
            raise ValueError(f"unfinished checkpoint exists for {job_id}; use resume")
        with paths["checkpoint"].open("rb") as handle:
            state = pickle.load(handle)
        validate_identity(state, identity, expected_format="frobenius-packed-job-checkpoint")
        if state["cutoff"] != int(bound):
            raise ValueError("checkpoint integer bound differs")
    elif paths["raw"].exists():
        raise ValueError("completed raw file exists without its metadata or checkpoint")
    elif paths["partial"].exists() and not resume:
        raise ValueError("unfinished raw file exists; use resume to restart its uncommitted contents")

    if state is None:
        stack = [tuple(map(integer, initial_root))]
        checked = pruned = guard_rejections = 0
        maximum_stack = 1
        prior_elapsed = 0.0
        committed_bytes = 0
        source = paths["partial"]
        mode = "w+b"
    else:
        stack = [tuple(map(integer, triple)) for triple in state["stack"]]
        checked, pruned = state["checked"], state["pruned"]
        guard_rejections, maximum_stack = state["guard_rejections"], state["maximum_stack"]
        prior_elapsed = state["elapsed_seconds"]
        committed_bytes = state["committed_bytes"]
        if (not isinstance(checked, int) or checked < 0 or
                committed_bytes != checked * RECORD_BYTES or
                pruned != checked + 1 - len(stack) or state["completed"] != (not stack)):
            raise ValueError("inconsistent packed checkpoint counts or frontier")
        source = paths["partial"] if paths["partial"].exists() else paths["raw"]
        if not source.is_file() or source.stat().st_size < committed_bytes:
            raise ValueError("raw file is shorter than the committed checkpoint")
        if source == paths["raw"] and stack:
            raise ValueError("unfinished checkpoint has an already finalized raw file")
        mode = "r+b"
    digest = hashlib.sha256()
    buffer = bytearray()
    buffer_limit = buffer_records * RECORD_BYTES
    next_progress = ((checked // progress_every + 1) * progress_every if progress_every else None)
    next_clock_check = checked + 100_000
    next_checkpoint = time.perf_counter() + checkpoint_seconds

    with source.open(mode) as output:
        output.truncate(committed_bytes)
        output.seek(0)
        remaining = committed_bytes
        while remaining:
            block = output.read(min(8 * 1024 * 1024, remaining))
            if not block:
                raise ValueError("cannot read committed raw prefix")
            digest.update(block)
            remaining -= len(block)
        output.seek(committed_bytes)

        def flush_buffer() -> None:
            if buffer:
                written = output.write(buffer)
                if written != len(buffer):
                    raise OSError("short write while generating packed residues")
                digest.update(buffer)
                buffer.clear()

        def checkpoint() -> None:
            flush_buffer()
            output.flush()
            os.fsync(output.fileno())
            if output.tell() != checked * RECORD_BYTES:
                raise RuntimeError("raw records and traversal count differ")
            atomic_write(paths["checkpoint"], {
                "format": "frobenius-packed-job-checkpoint", **identity,
                "created_utc": datetime.now(timezone.utc).isoformat(),
                "backend_version": backend_version, "cutoff": int(bound),
                "stack": [tuple(map(int, triple)) for triple in stack],
                "checked": checked, "pruned": pruned,
                "guard_rejections": guard_rejections, "maximum_stack": maximum_stack,
                "committed_bytes": checked * RECORD_BYTES,
                "committed_sha256": digest.hexdigest(),
                "elapsed_seconds": prior_elapsed + time.perf_counter() - started,
                "completed": not stack,
            }, binary=True)

        if state is not None and digest.hexdigest() != state["committed_sha256"]:
            raise ValueError("committed raw prefix checksum differs from its checkpoint")
        while stack:
            a, b, c = stack.pop()
            buffer.extend(int(c & mask).to_bytes(RECORD_BYTES, "little"))
            checked += 1
            c_bits = c.bit_length()
            # Since a < b, failure of the first guard also rejects the
            # second child. Avoid even allocating 3*c for such leaves.
            if a.bit_length() + c_bits > bound_bits:
                pruned += 2
                guard_rejections += 2
            else:
                three_c = 3 * c
                largest = a * three_c - b
                if largest <= bound:
                    stack.append((a, c, largest))
                else:
                    pruned += 1
                if b.bit_length() + c_bits <= bound_bits:
                    largest = b * three_c - a
                    if largest <= bound:
                        stack.append((b, c, largest))
                    else:
                        pruned += 1
                else:
                    pruned += 1
                    guard_rejections += 1
            if len(stack) > maximum_stack:
                maximum_stack = len(stack)
            if len(buffer) >= buffer_limit:
                flush_buffer()
            if next_progress is not None and checked >= next_progress:
                elapsed = prior_elapsed + time.perf_counter() - started
                print(f"{job_id}: generated {checked:,} residues; elapsed {elapsed:.1f}s; "
                      f"pending roots {len(stack):,}", flush=True)
                next_progress += progress_every
            if checked >= next_clock_check:
                now = time.perf_counter()
                if now >= next_checkpoint:
                    checkpoint()
                    print(f"{job_id}: durable checkpoint at {checked:,} records", flush=True)
                    next_checkpoint = now + checkpoint_seconds
                next_clock_check = checked + 100_000
            if stop_after is not None and checked >= stop_after:
                break
        if pruned != checked + 1 - len(stack):
            raise RuntimeError("inconsistent packed traversal frontier")
        checkpoint()
    elapsed = prior_elapsed + time.perf_counter() - started
    statistics = {
        "strict_triples": checked, "pruned_children": pruned,
        "products_avoided_by_bit_length_guard": guard_rejections,
        "maximum_pending_stack_entries": maximum_stack,
        "counting_seconds": elapsed,
    }
    if stack:
        return {
            "format": "frobenius-packed-partial-job", **identity, "completed": False,
            "records": checked, "size_bytes": checked * RECORD_BYTES,
            "raw_path": str(paths["partial"]), "statistics": statistics,
        }
    if source != paths["raw"]:
        os.replace(paths["partial"], paths["raw"])
    metadata = {
        "format": "frobenius-packed-job-metadata", **identity,
        "created_utc": datetime.now(timezone.utc).isoformat(), "completed": True,
        "backend_version": backend_version, "raw_path": str(paths["raw"]),
        "records": checked, "size_bytes": checked * RECORD_BYTES,
        "sha256": digest.hexdigest(), "statistics": statistics,
    }
    validate_completed(metadata, identity, paths["raw"])
    atomic_write(paths["metadata"], metadata, binary=False)
    return metadata


def initialize_worker(configuration: dict) -> None:
    """Initialize a spawn worker; reuse its exact bound across all jobs."""
    global WORKER_CONFIGURATION
    WORKER_CONFIGURATION = dict(configuration)
    prepare_bound(configuration["max_exponent"], configuration.get("backend", "gmpy2"))


def count_job(job: dict) -> dict:
    configuration = WORKER_CONFIGURATION
    return generate_job(
        configuration["max_exponent"], tuple(job["root"]), job["id"],
        configuration["configuration_id"], Path(configuration["workdir"]),
        backend=configuration.get("backend", "gmpy2"),
        buffer_records=configuration.get("buffer_records", 1_000_000),
        checkpoint_seconds=configuration.get("checkpoint_seconds", 300),
        progress_every=configuration.get("progress_every", 5_000_000),
        resume=configuration.get("resume", False))
