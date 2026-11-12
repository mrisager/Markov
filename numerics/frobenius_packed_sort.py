#!/usr/bin/env python3
"""Globally find repeated 128-bit signatures in packed Markov-number files.

Input records are 16 bytes: little-endian unsigned low64, then high64.
The caller supplies all files, including prefix nodes and exceptions.
Repeated signatures are candidates for exact replay, not counterexamples.

Sources are globally sharded by successive most-significant residue bytes.
An in-place NumPy sort handles bounded leaves; recursive radix splitting
handles oversized leaves without an unbounded Python set or array.
Candidate records are 24 bytes: little-endian low64, high64, occurrences.
Checkpoints commit each input file and each completed sorting node.
"""

from __future__ import annotations

from collections import OrderedDict
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import struct
import tempfile
import time
from typing import Iterator


SCHEMA_VERSION = 1
RECORD_BYTES = 16
CANDIDATE_BYTES = 24
EMPTY_SHA256 = hashlib.sha256(b"").hexdigest()
CANDIDATE_STRUCT = struct.Struct("<QQQ")


def _sync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _atomic_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=path.parent,
                                         prefix=f".{path.name}.", delete=False) as handle:
            temporary = Path(handle.name)
            json.dump(value, handle, indent=2)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
        _sync_directory(path.parent)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def _load_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def _hash_file(path: Path, chunk_bytes: int = 8 * 1024**2) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(chunk_bytes):
            digest.update(block)
    return digest.hexdigest()


def _fsync_paths(paths) -> None:
    directories = set()
    for path in paths:
        with path.open("rb") as handle:
            os.fsync(handle.fileno())
        directories.add(path.parent)
    for directory in directories:
        _sync_directory(directory)


class _BucketWriter:
    """Limit open streams even on machines with a small descriptor limit."""
    def __init__(self, directory: Path, maximum_open: int = 64):
        self.directory = directory
        self.maximum_open = maximum_open
        self.streams = OrderedDict()
        self.touched = set()

    def write(self, node_id: str, block) -> None:
        if node_id in self.streams:
            handle = self.streams.pop(node_id)
        else:
            if len(self.streams) >= self.maximum_open:
                _, old = self.streams.popitem(last=False)
                old.close()
            handle = (self.directory / f"{node_id}.bin").open("ab")
        self.streams[node_id] = handle
        self.touched.add(node_id)
        handle.write(block)

    def close(self, durable: bool = False) -> None:
        while self.streams:
            _, handle = self.streams.popitem()
            handle.close()
        if durable:
            _fsync_paths(self.directory / f"{node_id}.bin" for node_id in self.touched)


def _write_chunk(payload: bytes, prefix: str, writer: _BucketWriter,
                 sizes: list[int], hashes: list, np) -> None:
    if len(payload) % RECORD_BYTES:
        raise ValueError("truncated packed record")
    # Stable byte grouping is linear for these unsigned-byte keys.  It
    # preserves source order within each bucket for reproducible hashes.
    byte_index = 15 - len(prefix) // 2
    ids = np.frombuffer(payload, dtype=np.uint8)[byte_index::RECORD_BYTES]
    order = np.argsort(ids, kind="stable")
    pairs = np.frombuffer(payload, dtype=np.dtype([("low", "<u8"), ("high", "<u8")]))
    grouped = pairs[order]
    raw = memoryview(grouped).cast("B")
    counts = np.bincount(ids, minlength=256)
    position = 0
    for number, count in enumerate(counts):
        if not count:
            continue
        length = int(count) * RECORD_BYTES
        block = raw[position:position + length]
        writer.write(prefix + f"{number:02x}", block)
        sizes[number] += length
        hashes[number].update(block)
        position += length
    if position != len(payload):
        raise RuntimeError("inconsistent radix partition")


def _progress(workdir: Path, phase: str, total_records: int, **fields) -> None:
    _atomic_json(workdir / "progress.json", {
        "phase": phase, "total_records": total_records,
        "updated_utc": datetime.now(timezone.utc).isoformat(), **fields,
    })


def _validate_inputs(inputs: list[dict], workdir: Path) -> list[dict]:
    canonical = []
    used = set()
    for item in inputs:
        path = Path(item["path"]).resolve()
        count = item["records"]
        digest = item["sha256"].lower()
        if not isinstance(count, int) or isinstance(count, bool) or count < 0:
            raise ValueError("input record counts must be non-negative integers")
        if not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise ValueError("input sha256 must be a 64-digit hexadecimal string")
        if path in used:
            raise ValueError(f"input path supplied more than once: {path}")
        if path.is_relative_to(workdir / "data") or path.is_relative_to(workdir / "nodes"):
            raise ValueError("input files must not be in sorter scratch directories")
        if path.stat().st_size != count * RECORD_BYTES:
            raise ValueError(f"input byte count does not match declared records: {path}")
        used.add(path)
        canonical.append({"path": str(path), "records": count, "sha256": digest})
    return canonical


def _restore_shards(workdir: Path, manifest: dict):
    """Discard an interrupted input's tails and verify committed shards."""
    hashes = []
    for number, size in enumerate(manifest["bucket_bytes"]):
        path = workdir / "data" / f"{number:02x}.bin"
        actual = path.stat().st_size if path.exists() else 0
        if actual < size:
            raise ValueError(f"committed shard is truncated: {path}")
        if actual > size:
            with path.open("r+b") as handle:
                handle.truncate(size)
                handle.flush()
                os.fsync(handle.fileno())
        digest = hashlib.sha256()
        if size:
            with path.open("rb") as handle:
                while block := handle.read(8 * 1024**2):
                    digest.update(block)
        if digest.hexdigest() != manifest["bucket_sha256"][number]:
            raise ValueError(f"committed shard hash mismatch: {path}")
        hashes.append(digest)
    return hashes


def _shard_inputs(workdir: Path, manifest: dict, chunk_records: int, np) -> None:
    hashes = _restore_shards(workdir, manifest)
    total = manifest["total_records"]
    for index in range(manifest["next_input"], len(manifest["inputs"])):
        item = manifest["inputs"][index]
        before_sizes = list(manifest["bucket_bytes"])
        sizes = list(before_sizes)
        writer = _BucketWriter(workdir / "data")
        digest = hashlib.sha256()
        read_bytes = 0
        started = last_report = time.perf_counter()
        try:
            with Path(item["path"]).open("rb") as handle:
                while block := handle.read(chunk_records * RECORD_BYTES):
                    digest.update(block)
                    _write_chunk(block, "", writer, sizes, hashes, np)
                    read_bytes += len(block)
                    now = time.perf_counter()
                    if now - last_report >= 10:
                        _progress(workdir, "sharding", total,
                                  committed_records=manifest["committed_records"],
                                  current_input=index, current_input_bytes=read_bytes,
                                  current_input_size=item["records"] * RECORD_BYTES)
                        last_report = now
            if read_bytes != item["records"] * RECORD_BYTES:
                raise ValueError(f"input changed size during read: {item['path']}")
            if digest.hexdigest() != item["sha256"]:
                raise ValueError(f"input SHA-256 mismatch: {item['path']}")
            writer.close(durable=True)
        except BaseException:
            writer.close()
            for number, size in enumerate(before_sizes):
                path = workdir / "data" / f"{number:02x}.bin"
                if path.exists():
                    with path.open("r+b") as handle:
                        handle.truncate(size)
            raise
        manifest["bucket_bytes"] = sizes
        manifest["bucket_sha256"] = [digest.hexdigest() for digest in hashes]
        manifest["next_input"] = index + 1
        manifest["committed_records"] += item["records"]
        manifest["sharding_seconds"] += time.perf_counter() - started
        _atomic_json(workdir / "manifest.json", manifest)
        _progress(workdir, "sharding", total, committed_records=manifest["committed_records"],
                  completed_inputs=index + 1, total_inputs=len(manifest["inputs"]))
    if sum(manifest["bucket_bytes"]) != total * RECORD_BYTES:
        raise RuntimeError("global shard total does not match input records")
    manifest["phase"] = "sorting"
    _atomic_json(workdir / "manifest.json", manifest)


def _candidate_path(workdir: Path, node_id: str) -> Path:
    return workdir / "nodes" / f"{node_id}.candidates.bin"


def _validate_leaf(workdir: Path, node: dict) -> None:
    path = _candidate_path(workdir, node["node_id"])
    if path.stat().st_size != node["duplicate_signature_count"] * CANDIDATE_BYTES:
        raise ValueError(f"candidate file has wrong size: {path}")
    if _hash_file(path) != node["candidate_sha256"]:
        raise ValueError(f"candidate file hash mismatch: {path}")


def _write_candidates(workdir: Path, node_id: str, candidates) -> dict:
    path = _candidate_path(workdir, node_id)
    temporary = path.with_name(path.name + ".partial")
    digest = hashlib.sha256()
    groups = repeated = records_in_groups = 0
    buffer = bytearray()
    with temporary.open("wb") as handle:
        for low, high, occurrences in candidates:
            if not 2 <= occurrences < 2**64:
                raise ValueError("invalid duplicate group size")
            buffer.extend(CANDIDATE_STRUCT.pack(low, high, occurrences))
            groups += 1
            repeated += occurrences - 1
            records_in_groups += occurrences
            if len(buffer) >= 384 * 1024:
                handle.write(buffer)
                digest.update(buffer)
                buffer.clear()
        if buffer:
            handle.write(buffer)
            digest.update(buffer)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)
    return {"duplicate_signature_count": groups, "repeated_record_count": repeated,
            "records_in_duplicate_groups": records_in_groups,
            "candidate_sha256": digest.hexdigest()}


def _sort_leaf(workdir: Path, node_id: str, count: int, expected_hash: str, np) -> dict:
    source = workdir / "data" / f"{node_id}.bin"
    dtype = np.dtype([("low", "<u8"), ("high", "<u8")])
    pairs = np.fromfile(source, dtype=dtype)
    if len(pairs) != count or pairs.nbytes != source.stat().st_size:
        raise ValueError(f"leaf byte count mismatch: {source}")
    if hashlib.sha256(memoryview(pairs).cast("B")).hexdigest() != expected_hash:
        raise ValueError(f"leaf SHA-256 mismatch: {source}")
    pairs.sort(order=["high", "low"], kind="quicksort")
    equal = ((pairs["high"][1:] == pairs["high"][:-1]) &
             (pairs["low"][1:] == pairs["low"][:-1]))
    padded = np.empty(len(equal) + 2, dtype=np.bool_)
    padded[0] = padded[-1] = False
    padded[1:-1] = equal
    edges = np.flatnonzero(padded[1:] != padded[:-1])

    def candidates():
        for index in range(0, len(edges), 2):
            first, stop = int(edges[index]), int(edges[index + 1])
            yield int(pairs["low"][first]), int(pairs["high"][first]), stop - first + 1

    return _write_candidates(workdir, node_id, candidates())


def _split_node(workdir: Path, node_id: str, count: int, expected_hash: str,
                chunk_records: int, np) -> tuple[list[dict], int | None]:
    # An interrupted split has no committed node manifest; its children
    # are disposable.  The complete parent is retained until commitment.
    for number in range(256):
        (workdir / "data" / f"{node_id}{number:02x}.bin").unlink(missing_ok=True)
    source = workdir / "data" / f"{node_id}.bin"
    if source.stat().st_size != count * RECORD_BYTES:
        raise ValueError(f"oversized shard byte count mismatch: {source}")
    sizes = [0] * 256
    hashes = [hashlib.sha256() for _ in range(256)]
    digest = hashlib.sha256()
    writer = _BucketWriter(workdir / "data")
    first_record = None
    homogeneous = True
    try:
        with source.open("rb") as handle:
            while block := handle.read(chunk_records * RECORD_BYTES):
                digest.update(block)
                if first_record is None:
                    first_record = block[:RECORD_BYTES]
                if homogeneous:
                    raw = np.frombuffer(block, dtype=np.uint8).reshape(-1, RECORD_BYTES)
                    homogeneous = bool(np.all(raw == np.frombuffer(first_record, dtype=np.uint8)))
                _write_chunk(block, node_id, writer, sizes, hashes, np)
        if digest.hexdigest() != expected_hash or sum(sizes) != count * RECORD_BYTES:
            raise ValueError(f"oversized shard hash/count mismatch: {source}")
        writer.close(durable=True)
    except BaseException:
        writer.close()
        raise
    children = [{"node_id": node_id + f"{number:02x}", "records": size // RECORD_BYTES,
                 "sha256": hashes[number].hexdigest()}
                for number, size in enumerate(sizes) if size]
    residue = int.from_bytes(first_record, "little") if homogeneous and first_record is not None else None
    return children, residue


def _process_node(workdir: Path, node_id: str, count: int, expected_hash: str,
                  leaf_bytes: int, chunk_records: int, np) -> dict:
    state_path = workdir / "nodes" / f"{node_id}.json"
    source = workdir / "data" / f"{node_id}.bin"
    node = _load_json(state_path) if state_path.exists() else None
    if node is not None:
        if (node.get("schema_version") != SCHEMA_VERSION or node.get("node_id") != node_id or
                node.get("input_records") != count or node.get("input_sha256") != expected_hash):
            raise ValueError(f"sorting node identity mismatch: {state_path}")
        if node["kind"] == "leaf":
            _validate_leaf(workdir, node)
            for child_id in node.get("temporary_children", []):
                (workdir / "data" / f"{child_id}.bin").unlink(missing_ok=True)
            source.unlink(missing_ok=True)
            return node
        if node["kind"] != "split":
            raise ValueError(f"unknown sorting node kind: {state_path}")
    else:
        base = {"schema_version": SCHEMA_VERSION, "node_id": node_id,
                "input_records": count, "input_sha256": expected_hash}
        if count * RECORD_BYTES <= leaf_bytes:
            summary = _sort_leaf(workdir, node_id, count, expected_hash, np)
            node = {**base, "kind": "leaf", "completed": True, **summary}
            _atomic_json(state_path, node)
            source.unlink()
            return node
        if len(node_id) == 32:
            # All 16 prefix bytes fix the entire signature.  Stream its
            # hash rather than allocate an array proportional to its size.
            if source.stat().st_size != count * RECORD_BYTES or _hash_file(source) != expected_hash:
                raise ValueError(f"terminal shard hash/count mismatch: {source}")
            residue = int(node_id, 16)
            summary = _write_candidates(workdir, node_id,
                                        [(residue & (2**64 - 1), residue >> 64, count)])
            node = {**base, "kind": "leaf", "completed": True, **summary}
            _atomic_json(state_path, node)
            source.unlink()
            return node
        children, homogeneous = _split_node(workdir, node_id, count, expected_hash, chunk_records, np)
        if homogeneous is not None:
            summary = _write_candidates(workdir, node_id,
                                        [(homogeneous & (2**64 - 1), homogeneous >> 64, count)])
            node = {**base, "kind": "leaf", "completed": True, **summary,
                    "temporary_children": [child["node_id"] for child in children]}
            _atomic_json(state_path, node)
            for child in children:
                (workdir / "data" / f"{child['node_id']}.bin").unlink()
            source.unlink()
            return node
        node = {**base, "kind": "split", "completed": False, "children": children}
        _atomic_json(state_path, node)
    source.unlink(missing_ok=True)
    totals = {key: 0 for key in ("duplicate_signature_count", "repeated_record_count",
                                 "records_in_duplicate_groups")}
    child_records = 0
    for child in node["children"]:
        summary = _process_node(workdir, child["node_id"], child["records"], child["sha256"],
                                leaf_bytes, chunk_records, np)
        child_records += summary["input_records"]
        for key in totals:
            totals[key] += summary[key]
    if child_records != count:
        raise RuntimeError("recursive split lost records")
    node.update({"completed": True, **totals})
    _atomic_json(state_path, node)
    return node


def _leaf_nodes(workdir: Path, node_id: str):
    node = _load_json(workdir / "nodes" / f"{node_id}.json")
    if not node["completed"]:
        raise ValueError("sorting node is incomplete")
    if node["kind"] == "leaf":
        yield node
    else:
        for child in node["children"]:
            yield from _leaf_nodes(workdir, child["node_id"])


def _assemble_candidates(workdir: Path, manifest: dict) -> tuple[str, str]:
    path = workdir / "candidates.bin"
    temporary = path.with_name(path.name + ".partial")
    digest = hashlib.sha256()
    written_groups = 0
    with temporary.open("wb") as destination:
        for number, size in enumerate(manifest["bucket_bytes"]):
            if not size:
                continue
            for leaf in _leaf_nodes(workdir, f"{number:02x}"):
                source = _candidate_path(workdir, leaf["node_id"])
                if source.stat().st_size != leaf["duplicate_signature_count"] * CANDIDATE_BYTES:
                    raise ValueError("candidate leaf size mismatch during assembly")
                local_digest = hashlib.sha256()
                with source.open("rb") as handle:
                    while block := handle.read(8 * 1024**2):
                        local_digest.update(block)
                        digest.update(block)
                        destination.write(block)
                if local_digest.hexdigest() != leaf["candidate_sha256"]:
                    raise ValueError("candidate leaf hash mismatch during assembly")
                written_groups += leaf["duplicate_signature_count"]
        destination.flush()
        os.fsync(destination.fileno())
    if written_groups != manifest["duplicate_signature_count"]:
        raise RuntimeError("assembled candidate total mismatch")
    os.replace(temporary, path)
    return str(path), digest.hexdigest()


def _validate_report(workdir: Path, report: dict, config_id: str) -> None:
    if report.get("configuration_id") != config_id or not report.get("completed"):
        raise ValueError("completed sort report identity mismatch")
    path = workdir / "candidates.bin"
    if path.stat().st_size != report["duplicate_signature_count"] * CANDIDATE_BYTES:
        raise ValueError("completed candidate file size mismatch")
    if _hash_file(path) != report["candidate_sha256"]:
        raise ValueError("completed candidate file hash mismatch")


def sort_records(inputs: list[dict], workdir: Path, config_id: str, *,
                 resume: bool = True, max_memory_bytes: int = 512 * 1024**2) -> dict:
    """Find all globally repeated signatures in the supplied input files.

    Each input dict supplies path, records, and sha256.  Include exceptions
    and partition-prefix records yourself.  Memory is bounded by modest
    chunk buffers and leaves <= one sixth of max_memory_bytes, leaving
    room for NumPy's duplicate-boundary arrays and interpreter overhead.
    Original input files are always retained.  Check progress.json for
    live progress, and use iter_candidates on the returned candidates_path.
    """
    if not isinstance(max_memory_bytes, int) or max_memory_bytes < 1024:
        raise ValueError("max_memory_bytes must be an integer >= 1024")
    if not isinstance(config_id, str) or not config_id:
        raise ValueError("config_id must be a nonempty string")
    workdir = Path(workdir).resolve()
    canonical = _validate_inputs(inputs, workdir)
    workdir.mkdir(parents=True, exist_ok=True)
    manifest_path = workdir / "manifest.json"
    if manifest_path.exists():
        if not resume:
            raise ValueError("sort workdir already contains a manifest; use resume")
        manifest = _load_json(manifest_path)
        if (manifest.get("schema_version") != SCHEMA_VERSION or
                manifest.get("configuration_id") != config_id or manifest.get("inputs") != canonical):
            raise ValueError("sort manifest does not match requested configuration or inputs")
        if manifest["phase"] == "complete":
            report = _load_json(workdir / "report.json")
            _validate_report(workdir, report, config_id)
            return report
    else:
        if (workdir / "data").exists() or (workdir / "nodes").exists():
            raise ValueError("scratch directories already exist without a manifest")
        manifest = {
            "schema_version": SCHEMA_VERSION, "format": "frobenius-packed-sort",
            "configuration_id": config_id, "inputs": canonical,
            "input_format": "16 bytes: little-endian unsigned low64, high64",
            "candidate_format": "24 bytes: little-endian unsigned low64, high64, occurrences64",
            "total_records": sum(item["records"] for item in canonical),
            "phase": "sharding", "next_input": 0, "committed_records": 0,
            "bucket_bytes": [0] * 256, "bucket_sha256": [EMPTY_SHA256] * 256,
            "sorted_buckets": [], "duplicate_signature_count": 0,
            "repeated_record_count": 0, "records_in_duplicate_groups": 0,
            "sharding_seconds": 0.0, "sorting_seconds": 0.0,
        }
        _atomic_json(manifest_path, manifest)
    (workdir / "data").mkdir(exist_ok=True)
    (workdir / "nodes").mkdir(exist_ok=True)
    import numpy as np
    leaf_bytes = max(RECORD_BYTES, max_memory_bytes // 6 // RECORD_BYTES * RECORD_BYTES)
    chunk_records = max(1, min(1_000_000, max_memory_bytes // (RECORD_BYTES * 12)))
    if manifest["phase"] == "sharding":
        _shard_inputs(workdir, manifest, chunk_records, np)
    if manifest["phase"] != "sorting":
        raise ValueError("unknown sorting phase")
    totals = {key: 0 for key in ("duplicate_signature_count", "repeated_record_count",
                                 "records_in_duplicate_groups")}
    for number, size in enumerate(manifest["bucket_bytes"]):
        if not size:
            continue
        started = time.perf_counter()
        summary = _process_node(workdir, f"{number:02x}", size // RECORD_BYTES,
                                manifest["bucket_sha256"][number], leaf_bytes, chunk_records, np)
        for key in totals:
            totals[key] += summary[key]
        if number not in manifest["sorted_buckets"]:
            manifest["sorted_buckets"].append(number)
            manifest["sorting_seconds"] += time.perf_counter() - started
        manifest.update(totals)
        _atomic_json(manifest_path, manifest)
        _progress(workdir, "sorting", manifest["total_records"],
                  sorted_buckets=len(manifest["sorted_buckets"]), total_buckets=256,
                  duplicate_signature_count=totals["duplicate_signature_count"])
    if sum(manifest["bucket_bytes"]) != manifest["total_records"] * RECORD_BYTES:
        raise RuntimeError("sort record total mismatch")
    candidates_path, candidate_sha256 = _assemble_candidates(workdir, manifest)
    report = {
        "schema_version": SCHEMA_VERSION, "configuration_id": config_id, "completed": True,
        "total_records": manifest["total_records"], **totals,
        "repeated_record_count_definition": "sum(occurrences - 1) over repeated-signature groups",
        "candidates_path": candidates_path, "candidate_sha256": candidate_sha256,
        "candidate_format": manifest["candidate_format"],
        "sharding_seconds": manifest["sharding_seconds"],
        "sorting_seconds": manifest["sorting_seconds"], "max_memory_bytes": max_memory_bytes,
        "maximum_leaf_bytes": leaf_bytes, "scratch_cleaned": False,
        "scope": "128-bit residues only; repeated signatures require exact replay",
    }
    _atomic_json(workdir / "report.json", report)
    manifest["phase"] = "complete"
    _atomic_json(manifest_path, manifest)
    _progress(workdir, "complete", manifest["total_records"],
              duplicate_signature_count=totals["duplicate_signature_count"],
              repeated_record_count=totals["repeated_record_count"])
    return report


def iter_candidates(path: Path) -> Iterator[tuple[int, int]]:
    """Yield ordered (residue, occurrences) from a completed candidate file."""
    path = Path(path)
    if path.stat().st_size % CANDIDATE_BYTES:
        raise ValueError("truncated candidate file")
    previous = -1
    with path.open("rb") as handle:
        while block := handle.read(CANDIDATE_BYTES * 16_384):
            if len(block) % CANDIDATE_BYTES:
                raise ValueError("candidate file changed size while reading")
            for low, high, occurrences in CANDIDATE_STRUCT.iter_unpack(block):
                residue = (high << 64) | low
                if occurrences < 2 or residue <= previous:
                    raise ValueError("candidate records must be strictly ordered duplicate groups")
                previous = residue
                yield residue, occurrences


def cleanup_sort_workdir(workdir: Path, config_id: str) -> None:
    """Remove sorter-owned scratch after the caller's exact replay succeeds.

    Original input files, node manifests, global candidates and reports
    are retained.  The completed report remains resumable after cleanup.
    """
    workdir = Path(workdir).resolve()
    report = _load_json(workdir / "report.json")
    _validate_report(workdir, report, config_id)
    manifest = _load_json(workdir / "manifest.json")
    if manifest.get("configuration_id") != config_id or manifest.get("phase") != "complete":
        raise ValueError("scratch cleanup requires a matching completed manifest")
    if (workdir / "data").exists():
        shutil.rmtree(workdir / "data", ignore_errors=False)
    for path in (workdir / "nodes").glob("*.candidates.bin"):
        path.unlink()
    report["scratch_cleaned"] = True
    _atomic_json(workdir / "report.json", report)
