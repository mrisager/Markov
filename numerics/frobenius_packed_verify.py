#!/usr/bin/env python3
"""Exhaustively verify Frobenius uniqueness with exact packed residues.

Enumerate disjoint strict Markov-tree subtrees using exact integers, store
the largest coordinates modulo 2**128 as packed 16-byte records, and sort
them globally in bounded-memory disk buckets. Equal full integers must have
equal residues: no repeated residue is an exact uniqueness certificate,
without any assumption about the probability of a residue collision.
Repeated residues are resolved by an independent exact traversal.

Example:
    python frobenius_packed_verify.py --max-exponent 30000 --workers 6
    python frobenius_packed_verify.py --max-exponent 30000 --workers 6 --resume
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import math
import multiprocessing
from pathlib import Path
import shutil
import sys
import time

import frobenius_packed_generate as generation
import frobenius_packed_sort as sorting
import markov_error_parallel as partitioning
import markov_error_plot as counting


SCHEMA_VERSION = 1
ALGORITHM = "exact-markov-tree-packed-residue-global-sort-v1"
MASK = (1 << 128) - 1
RECORD_SIZE = 16


def source_checksums() -> dict:
    modules = (Path(__file__), Path(generation.__file__), Path(sorting.__file__),
               Path(partitioning.__file__), Path(counting.__file__))
    return {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in modules}


def identity(value) -> str:
    return partitioning.checksum(value)


def write_json(path: Path, value: dict) -> None:
    partitioning.write_json(path, value)


def file_digest(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(8 * 1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def prefix_residues(exponent: int, jobs: list[dict], expected: dict, backend: str):
    """Visit all expanded ancestors once, stopping at the frontier roots."""
    integer, _, _ = counting.select_backend(backend)
    bound = integer(10) ** exponent
    root = tuple(integer(c) for c in (1, 2, 5))
    frontier = {job["path"]: tuple(job["root"]) for job in jobs}
    if len(frontier) != len(jobs):
        raise ValueError("duplicate partition paths")
    paths = sorted(frontier)
    if any(b.startswith(a) for a, b in zip(paths, paths[1:])):
        raise ValueError("partition roots are not prefix-free")
    stack = [("", root)] if root[2] <= bound else []
    residues, encountered = [], set()
    pruned = 0
    while stack:
        path, (a, b, c) = stack.pop()
        if path in frontier:
            if tuple(int(value) for value in (a, b, c)) != frontier[path]:
                raise ValueError("partition path and root disagree")
            encountered.add(path)
            continue
        residues.append(int(c & MASK))
        for bit, small, subtraction in (("0", a, b), ("1", b, a)):
            child = 3 * small * c - subtraction
            if child <= bound:
                stack.append((path + bit, (small, c, child)))
            else:
                pruned += 1
    if (encountered != set(frontier) or len(residues) != expected["strict_triples"]
            or pruned != expected["pruned_children"]
            or pruned != len(residues) + 1 - len(jobs)):
        raise RuntimeError("independent prefix traversal disagrees with partition")
    return residues


def write_prefix(directory: Path, residues: list[int], configuration_id: str,
                 *, resume: bool) -> dict:
    """Include both exceptional triples in the same global residue check."""
    path = directory / "prefix-and-exceptions.bin"
    data = b"".join(value.to_bytes(RECORD_SIZE, "little") for value in [1, 2, *residues])
    expected = {"path": str(path), "records": len(residues) + 2,
                "size_bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(),
                "configuration_id": configuration_id}
    if resume and path.exists():
        if path.read_bytes() != data:
            raise ValueError("saved prefix records differ from this partition")
    else:
        temporary = path.with_suffix(".tmp")
        with temporary.open("wb") as handle:
            handle.write(data)
            handle.flush()
            import os
            os.fsync(handle.fileno())
        temporary.replace(path)
    write_json(directory / "prefix-and-exceptions.json", expected)
    return expected


def validate_job(result: dict, job: dict, configuration_id: str, exponent: int,
                 backend: str) -> None:
    stats = result["statistics"]
    if (not result["completed"] or result["configuration_id"] != configuration_id
            or result["job_id"] != job["id"] or result["initial_root"] != job["root"]
            or result["max_exponent"] != exponent or result["backend"] != backend
            or result["records"] != stats["strict_triples"]
            or result["size_bytes"] != RECORD_SIZE * result["records"]
            or stats["pruned_children"] != result["records"] + 1
            or Path(result["raw_path"]).stat().st_size != result["size_bytes"]):
        raise ValueError(f"invalid completed job: {job['id']}")


def historical_expected(exponent: int) -> dict | None:
    path = Path(__file__).parent / f"markov-error-10e{exponent}.json"
    if not path.exists():
        return None
    data = json.loads(path.read_text())
    if data.get("maximum_cutoff") != f"10^{exponent}" or not data.get("completed", True):
        raise ValueError("previous count metadata has an unexpected cutoff or status")
    return {"path": str(path.resolve()), "sha256": file_digest(path),
            "strict_triples": data["strict_triples"],
            "triples_including_exceptions": data["triples_including_exceptions"]}


def exact_replay(exponent: int, candidates, backend: str,
                 progress_every: int = 5_000_000) -> dict:
    """Resolve candidate residues using exact largest coordinates and triples."""
    integer, _, _ = counting.select_backend(backend)
    bound = integer(10) ** exponent
    bound_bits = bound.bit_length()
    mask = integer(MASK)
    expected = {}
    for residue, occurrences in candidates:
        if residue in expected or occurrences < 1:
            raise ValueError("duplicate or invalid candidate residue entry")
        expected[residue] = occurrences
    seen = {residue: {} for residue in expected}
    matches = {residue: 0 for residue in expected}
    counterexample = None

    def visit(a, b, c):
        nonlocal counterexample
        residue = int(c & mask)
        if residue not in expected:
            return
        matches[residue] += 1
        largest = int(c)
        triple = tuple(int(value) for value in (a, b, c))
        previous = seen[residue].get(largest)
        if previous is not None and previous != triple:
            counterexample = {
                "residue_hex": f"{residue:032x}",
                "first_triple_hex": [hex(value) for value in previous],
                "second_triple_hex": [hex(value) for value in triple],
                "largest_coordinate_hex": hex(largest),
                "largest_coordinate_bit_length": largest.bit_length(),
            }
        seen[residue][largest] = triple

    for a, b, c in ((1, 1, 1), (1, 1, 2)):
        visit(integer(a), integer(b), integer(c))
    stack = [tuple(integer(value) for value in (1, 2, 5))]
    checked, pruned, next_progress = 0, 0, progress_every
    started = time.perf_counter()
    while stack and counterexample is None:
        a, b, c = stack.pop()
        visit(a, b, c)
        checked += 1
        c_bits = c.bit_length()
        for small, subtraction in ((a, b), (b, a)):
            if small.bit_length() + c_bits > bound_bits:
                pruned += 1
                continue
            child = 3 * small * c - subtraction
            if child <= bound:
                stack.append((small, c, child))
            else:
                pruned += 1
        if progress_every and checked >= next_progress:
            print(f"Exact candidate replay: {checked:,} strict triples; "
                  f"elapsed {time.perf_counter() - started:.1f}s.", flush=True)
            next_progress += progress_every
    if counterexample is not None:
        return {"uniqueness_verified": False, "counterexample": counterexample,
                "strict_triples_checked": checked, "completed": False}
    if pruned != checked + 1 or matches != expected:
        raise RuntimeError("exact candidate replay multiplicities differ from packed records")
    return {"uniqueness_verified": True, "counterexample": None,
            "strict_triples_checked": checked, "completed": True,
            "candidate_signature_count": len(expected),
            "matched_occurrences": sum(matches.values()),
            "seconds": time.perf_counter() - started}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-exponent", type=counting.positive_int, default=30000)
    parser.add_argument("--workers", type=counting.positive_int, default=6)
    parser.add_argument("--tasks", type=counting.positive_int, default=64)
    parser.add_argument("--backend", choices=("gmpy2", "python", "auto"), default="auto")
    parser.add_argument("--workdir", type=Path)
    parser.add_argument("--output-prefix", type=Path)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--checkpoint-seconds", type=counting.positive_float, default=300)
    parser.add_argument("--progress-every", type=counting.non_negative_int, default=5_000_000)
    parser.add_argument("--buffer-records", type=counting.positive_int, default=1_000_000)
    parser.add_argument("--sort-memory-mib", type=counting.positive_int, default=512)
    args = parser.parse_args()
    started = time.perf_counter()
    created_utc = datetime.now(timezone.utc).isoformat()
    _, backend, backend_version = counting.select_backend(args.backend)
    base = Path(__file__).resolve().parent
    output_prefix = (args.output_prefix or base / f"frobenius-10e{args.max_exponent}").resolve()
    directory = (args.workdir or base / f".frobenius-10e{args.max_exponent}-work").resolve()
    directory.mkdir(parents=True, exist_ok=True)
    run_lock = (directory / "run.lock").open("a+")
    try:
        fcntl.flock(run_lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        parser.error("another verification process is already using this work directory")
    jobs, _, prefix_stats = partitioning.partition_tree([args.max_exponent], backend, args.tasks)
    counting.prepare_cutoffs.cache_clear()
    prefix = prefix_residues(args.max_exponent, jobs, prefix_stats, backend)
    expected = historical_expected(args.max_exponent)
    configuration = {
        "algorithm": ALGORITHM, "max_exponent": args.max_exponent, "backend": backend,
        "residue_bits": 128, "record_format": "16-byte unsigned little-endian integer; low64 then high64",
        "requested_tasks": args.tasks, "jobs": jobs, "prefix_statistics": prefix_stats,
        "prefix_residues_hex": [f"{value:032x}" for value in prefix],
        "exceptional_triples": [[1, 1, 1], [1, 1, 2]],
        "source_sha256": source_checksums(), "independent_count": expected,
    }
    configuration_id = identity(configuration)
    manifest_path = directory / "manifest.json"
    if manifest_path.exists():
        if not args.resume:
            parser.error(f"{manifest_path} exists; use --resume or a new work directory")
        manifest = json.loads(manifest_path.read_text())
        if (manifest.get("schema_version") != SCHEMA_VERSION
                or manifest.get("configuration_id") != configuration_id
                or manifest.get("configuration") != configuration):
            parser.error("saved manifest differs from the requested computation or source code")
    else:
        if args.resume:
            parser.error("no saved manifest exists for this --resume request")
        if any(path.name != "run.lock" for path in directory.iterdir()):
            parser.error("work directory is non-empty without a matching manifest")
        directory.mkdir(parents=True, exist_ok=True)
        estimated_records = (expected["triples_including_exceptions"] if expected else
                             math.ceil(1.05 * float(counting.CONSTANT_TEXT) *
                                       (args.max_exponent * math.log(10) + math.log(3)) ** 2) + 100)
        required = 2 * RECORD_SIZE * estimated_records + 4 * 1024**3
        free = shutil.disk_usage(directory).free
        if free < required:
            parser.error(f"need about {required / 1024**3:.1f} GiB free for records, sorting and reserve; "
                         f"only {free / 1024**3:.1f} GiB is available")
        write_json(manifest_path, {"format": "frobenius-packed-verification-manifest",
                                  "schema_version": SCHEMA_VERSION,
                                  "created_utc": created_utc, "configuration": configuration,
                                  "configuration_id": configuration_id})
    raw_directory = directory / "records"
    raw_directory.mkdir(exist_ok=True)
    prefix_input = write_prefix(raw_directory, prefix, configuration_id, resume=args.resume)
    worker_configuration = {
        "max_exponent": args.max_exponent, "configuration_id": configuration_id,
        "workdir": str(raw_directory), "backend": backend,
        "buffer_records": args.buffer_records, "checkpoint_seconds": args.checkpoint_seconds,
        "progress_every": args.progress_every, "resume": args.resume,
    }
    completed = {}
    job_by_id = {job["id"]: job for job in jobs}

    def progress(stage="generation", **extra):
        strict = prefix_stats["strict_triples"] + sum(item["records"] for item in completed.values())
        write_json(directory / "progress.json", {
            "configuration_id": configuration_id, "updated_utc": datetime.now(timezone.utc).isoformat(),
            "stage": stage, "completed_job_ids": sorted(completed),
            "completed_jobs": len(completed), "total_jobs": len(jobs),
            "strict_triples_in_completed_work": strict,
            "triples_including_exceptions_in_completed_work": strict + 2,
            "expected_strict_triples": expected["strict_triples"] if expected else None,
            "session_seconds": time.perf_counter() - started, **extra,
        })

    def merge(result):
        job_id = result["job_id"]
        if job_id in completed or job_id not in job_by_id:
            raise RuntimeError("duplicate or unexpected completed generation job")
        validate_job(result, job_by_id[job_id], configuration_id, args.max_exponent, backend)
        completed[job_id] = result
        progress()
        strict = prefix_stats["strict_triples"] + sum(item["records"] for item in completed.values())
        print(f"Completed {len(completed)}/{len(jobs)} generation jobs; "
              f"{strict:,} strict triples in completed work; wall {time.perf_counter() - started:.1f}s.",
              flush=True)

    pending = []
    for job in jobs:
        if (raw_directory / f"{job['id']}.metadata.json").exists():
            if not args.resume:
                raise ValueError("completed raw job found without --resume")
            merge(generation.generate_job(args.max_exponent, tuple(job["root"]), job["id"],
                                          configuration_id, raw_directory,
                                          backend=backend, resume=True))
        else:
            pending.append(job)
    pending.sort(key=lambda job: math.log(3 * job["root"][0]) * math.log(3 * job["root"][1]))
    generation_started = time.perf_counter()
    progress()
    print(f"Verifying largest coordinates through 10^{args.max_exponent}; "
          f"{len(jobs)} disjoint jobs, {len(prefix)} ancestor records, "
          f"two exceptional triples, {args.workers} workers.", flush=True)
    if pending:
        if args.workers == 1:
            generation.initialize_worker(worker_configuration)
            for job in pending:
                merge(generation.count_job(job))
        else:
            with multiprocessing.get_context("spawn").Pool(
                    min(args.workers, len(pending)), initializer=generation.initialize_worker,
                    initargs=(worker_configuration,)) as pool:
                for result in pool.imap_unordered(generation.count_job, pending, chunksize=1):
                    merge(result)
    strict_count = prefix_stats["strict_triples"] + sum(item["records"] for item in completed.values())
    pruned = prefix_stats["pruned_children"] + sum(
        item["statistics"]["pruned_children"] for item in completed.values())
    if len(completed) != len(jobs) or pruned != strict_count + 1:
        raise RuntimeError("generation forest is incomplete")
    if expected and strict_count != expected["strict_triples"]:
        raise RuntimeError("verification enumeration differs from the independent earlier count")
    generation_seconds = time.perf_counter() - generation_started
    inputs = [prefix_input] + [
        {"path": completed[job["id"]]["raw_path"], "records": completed[job["id"]]["records"],
         "size_bytes": completed[job["id"]]["size_bytes"],
         "sha256": completed[job["id"]]["sha256"]} for job in jobs]
    progress("global_sort", generation_completed=True)
    print(f"Enumeration complete: {strict_count:,} strict triples; "
          "checking packed residues globally across all jobs.", flush=True)
    # The sorting module verifies input byte counts and SHA256 while sharding.
    sort_result = sorting.sort_records(
        inputs, directory / "sort", configuration_id, resume=args.resume,
        max_memory_bytes=args.sort_memory_mib * 1024**2)
    if sort_result["total_records"] != strict_count + 2:
        raise RuntimeError("global sort record count differs from enumeration")
    replay = None
    unique_residues = sort_result["duplicate_signature_count"] == 0
    if unique_residues:
        uniqueness_verified = True
    else:
        progress("exact_candidate_replay", duplicate_signatures=sort_result["duplicate_signature_count"])
        replay = exact_replay(args.max_exponent,
                              sorting.iter_candidates(Path(sort_result["candidates_path"])),
                              backend, args.progress_every)
        uniqueness_verified = replay["uniqueness_verified"]
        if uniqueness_verified and replay["strict_triples_checked"] != strict_count:
            raise RuntimeError("independent candidate replay count differs from enumeration")
    output_prefix.parent.mkdir(parents=True, exist_ok=True)
    report = {
        "format": "frobenius-packed-verification-result", "schema_version": SCHEMA_VERSION,
        "created_utc": datetime.now(timezone.utc).isoformat(), "session_started_utc": created_utc,
        "maximum_cutoff": f"10^{args.max_exponent}",
        "counting_definition": "positive Markov triples a <= b <= c <= bound",
        "strict_triples": strict_count, "triples_including_exceptions": strict_count + 2,
        "exceptional_triples_included": [[1, 1, 1], [1, 1, 2]],
        "uniqueness_verified": uniqueness_verified, "distinct_residues_modulo_2_to_128": unique_residues,
        "certificate_logic": "Equal largest coordinates imply equal 128-bit residues; all residues are checked globally.",
        "cutoff_comparisons": "exact integer arithmetic with a proved bit-length rejection guard",
        "pruned_children": pruned, "completed": True,
        "backend": backend, "backend_version": backend_version,
        "workers": args.workers, "task_count": len(jobs), "prefix_strict_triples": len(prefix),
        "configuration_id": configuration_id, "source_sha256": configuration["source_sha256"],
        "work_directory": str(directory), "manifest": str(manifest_path),
        "independent_previous_count": expected, "previous_count_matched": bool(expected),
        "resumed": args.resume, "generation_session_seconds": generation_seconds,
        "total_session_seconds": time.perf_counter() - started,
        "generation_jobs": [completed[job["id"]] for job in jobs],
        "global_sort": sort_result, "exact_candidate_replay": replay,
    }
    write_json(output_prefix.with_suffix(".json"), report)
    sorting.cleanup_sort_workdir(directory / "sort", configuration_id)
    report["global_sort"]["scratch_cleaned"] = True
    write_json(output_prefix.with_suffix(".json"), report)
    message = (
        f"Frobenius uniqueness through 10^{args.max_exponent}: "
        f"{'VERIFIED' if uniqueness_verified else 'COUNTEREXAMPLE FOUND'}\n"
        f"Strict triples: {strict_count:,}\n"
        f"Triples including (1,1,1) and (1,1,2): {strict_count + 2:,}\n"
        f"Repeated 128-bit residue signatures: {sort_result['duplicate_signature_count']:,}\n"
        f"All residues distinct modulo 2^128: {unique_residues}\n"
        f"Exact cutoff comparisons: yes\n"
        f"Global comparison across all workers: yes\n"
        f"Independent prior count matched: {bool(expected)}\n"
        f"Current session wall time: {report['total_session_seconds']:.3f} seconds\n"
        f"Result metadata: {output_prefix.with_suffix('.json')}\n"
    )
    output_prefix.with_suffix(".txt").write_text(message)
    progress("complete", uniqueness_verified=uniqueness_verified,
             distinct_residues_modulo_2_to_128=unique_residues)
    print(message, flush=True)


if __name__ == "__main__":
    main()
