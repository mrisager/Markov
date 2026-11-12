#!/usr/bin/env python3
"""Count exact Markov triples in parallel and plot raw and normalized errors.

The frontier consists of disjoint subtrees of the strict Markov tree. A
floating-point weight balances their sizes; every cutoff comparison and
histogram count remains exact. The coordinator counts expanded prefix nodes
once, then merges each completed subtree once. The two exceptional triples
are added only when producing the final M(x) table.

Example::

    python markov_error_parallel.py --max-exponent 30000 --workers 6
    python markov_error_parallel.py --max-exponent 30000 --workers 6 --resume

Local checkpoints are trusted pickle files created by these counting scripts.
Workers use the portable spawn start method and prepare their cutoff table
once, reusing it for all subsequent jobs in the same process.
"""

from __future__ import annotations

import argparse
import csv
from datetime import datetime, timezone
from decimal import Decimal
import hashlib
import heapq
import json
import math
import multiprocessing
from pathlib import Path
import pickle
import sys
import tempfile
import os
import time

import markov_error_plot as plotting


SCHEMA_VERSION = 1
ALGORITHM = "strict-markov-tree-exact-bins-adaptive-frontier-v1"
WORKER_CONFIGURATION: dict = {}


def write_json(path: Path, value: dict) -> None:
    """Replace JSON atomically, including coordinator progress snapshots."""
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
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def checksum(value) -> str:
    data = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def partition_tree(exponents: list[int], backend: str, target: int):
    """Return a prefix histogram and a disjoint frontier below the bound.

    A scheduling weight 1/(log(3a)*log(3b)) repeatedly selects a promising
    large subtree to split. Its accuracy does not affect completeness.
    Splitting removes one root from the frontier, counts it in the prefix,
    and inserts exactly its children that satisfy the integer bound.
    """
    _, _, _, cutoffs, exponent_to_bin, bound_bits = plotting.prepare_cutoffs(
        tuple(exponents), backend)
    bound = cutoffs[-1]
    prefix_bins = [0] * len(exponents)
    prefix_checked = prefix_pruned = prefix_guards = 0

    def priority(root):
        a, b, _ = root
        return -1 / (math.log(3 * a) * math.log(3 * b))

    def add_to_prefix(c):
        proposed = min(exponents[-1], int((c.bit_length() - 1) * plotting.LOG10_2) + 1)
        index = exponent_to_bin[proposed]
        while c > cutoffs[index]:
            index += 1
        while index > 0 and c <= cutoffs[index - 1]:
            index -= 1
        prefix_bins[index] += 1

    root = (1, 2, 5)
    frontier = [(priority(root), "", root)]
    while frontier and len(frontier) < target:
        _, path, (a, b, c) = heapq.heappop(frontier)
        add_to_prefix(c)
        prefix_checked += 1
        c_bits = c.bit_length()
        for bit, small, subtraction in (("0", a, b), ("1", b, a)):
            if small.bit_length() + c_bits > bound_bits:
                prefix_pruned += 1
                prefix_guards += 1
                continue
            largest = 3 * small * c - subtraction
            if largest > bound:
                prefix_pruned += 1
                continue
            child = (small, c, largest)
            heapq.heappush(frontier, (priority(child), path + bit, child))
    jobs = [{"id": f"job-{index:05d}", "path": path, "root": list(root)}
            for index, (_, path, root) in enumerate(sorted(frontier, key=lambda item: item[1]))]
    if sum(prefix_bins) != prefix_checked or prefix_pruned != prefix_checked + 1 - len(jobs):
        raise RuntimeError("inconsistent partition frontier")
    paths = sorted(job["path"] for job in jobs)
    if any(second.startswith(first) for first, second in zip(paths, paths[1:])):
        raise RuntimeError("partition roots have overlapping subtrees")
    statistics = {
        "strict_triples": prefix_checked,
        "pruned_children": prefix_pruned,
        "products_avoided_by_bit_length_guard": prefix_guards,
    }
    return jobs, prefix_bins, statistics


def result_path(directory: Path, job: dict) -> Path:
    return directory / f"{job['id']}.result.pkl"


def validate_result(value: dict, job: dict, configuration_id: str,
                    sample_count: int, backend: str) -> None:
    if not isinstance(value, dict) or value.get("format") != "markov-parallel-subtree-result":
        raise ValueError("not a parallel Markov subtree result")
    if (value.get("schema_version") != SCHEMA_VERSION or
            value.get("configuration_id") != configuration_id or
            value.get("job_id") != job["id"] or value.get("root") != job["root"]):
        raise ValueError(f"saved result does not match {job['id']}")
    bins, stats = value["bins"], value["statistics"]
    if (len(bins) != sample_count or any(not isinstance(n, int) or n < 0 for n in bins) or
            not stats["completed"] or stats["initial_root_count"] != 1 or
            stats["backend"] != backend or sum(bins) != stats["strict_triples"] or
            stats["pruned_children"] != stats["strict_triples"] + 1):
        raise ValueError(f"inconsistent completed result for {job['id']}")


def load_result(path: Path, job: dict, configuration_id: str,
                sample_count: int, backend: str) -> dict:
    with path.open("rb") as handle:
        value = pickle.load(handle)
    validate_result(value, job, configuration_id, sample_count, backend)
    return value


def initialize_worker(configuration: dict) -> None:
    global WORKER_CONFIGURATION
    WORKER_CONFIGURATION = configuration
    plotting.prepare_cutoffs(tuple(configuration["exponents"]), configuration["backend"])


def count_job(job: dict) -> dict:
    configuration = WORKER_CONFIGURATION
    directory = Path(configuration["checkpoint_directory"])
    saved = result_path(directory, job)
    if saved.exists():
        return load_result(saved, job, configuration["configuration_id"],
                           len(configuration["exponents"]), configuration["backend"])
    checkpoint = directory / f"{job['id']}.checkpoint.pkl"
    bins, statistics = plotting.count_bins(
        configuration["exponents"], configuration["backend"],
        initial_stack=[tuple(job["root"])], checkpoint_path=checkpoint,
        resume=configuration["resume"] and checkpoint.exists(),
        checkpoint_seconds=configuration["checkpoint_seconds"],
        progress_every=configuration["progress_every"], progress_label=job["id"])
    value = {
        "format": "markov-parallel-subtree-result", "schema_version": SCHEMA_VERSION,
        "configuration_id": configuration["configuration_id"], "job_id": job["id"],
        "root": job["root"], "worker_pid": os.getpid(), "bins": bins,
        "statistics": statistics,
    }
    validate_result(value, job, configuration["configuration_id"],
                    len(configuration["exponents"]), configuration["backend"])
    plotting._write_checkpoint(saved, value)
    return value


def count_parallel(exponents: list[int], backend: str, workers: int, target_tasks: int,
                   directory: Path, *, resume: bool = False,
                   checkpoint_seconds: float = 300, progress_every: int = 5_000_000):
    """Merge each exact job result once; unfinished jobs never enter the total."""
    started = time.perf_counter()
    directory = directory.resolve()
    _, backend_name, backend_version = plotting.select_backend(backend)
    jobs, prefix_bins, prefix_statistics = partition_tree(exponents, backend_name, target_tasks)
    configuration = {
        "algorithm": ALGORITHM, "exponents": exponents, "backend": backend_name,
        "requested_tasks": target_tasks,
    }
    partition = {"jobs": jobs, "prefix_bins": prefix_bins,
                 "prefix_statistics": prefix_statistics}
    partition_id = checksum(partition)
    configuration_id = checksum({"configuration": configuration, "partition_id": partition_id})
    manifest_path = directory / "manifest.json"
    if manifest_path.exists():
        if not resume:
            raise ValueError(f"{manifest_path} already exists; use --resume or another checkpoint directory")
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        if (manifest.get("schema_version") != SCHEMA_VERSION or
                manifest.get("format") != "markov-parallel-manifest" or
                manifest.get("configuration_id") != configuration_id or
                manifest.get("configuration") != configuration or
                manifest.get("partition") != partition or
                manifest.get("partition_checksum") != partition_id):
            raise ValueError("checkpoint manifest differs from the requested forest or sampling")
    else:
        if resume:
            raise ValueError(f"no checkpoint manifest exists at {manifest_path}")
        if directory.exists() and any(directory.iterdir()):
            raise ValueError("checkpoint directory is non-empty without a matching manifest")
        write_json(manifest_path, {
            "format": "markov-parallel-manifest", "schema_version": SCHEMA_VERSION,
            "created_utc": datetime.now(timezone.utc).isoformat(),
            "configuration": configuration, "configuration_id": configuration_id,
            "partition_checksum": partition_id, "partition": partition,
        })
    # The coordinator needs only its small prefix histogram after partitioning.
    plotting.prepare_cutoffs.cache_clear()
    bins = list(prefix_bins)
    completed: dict[str, dict] = {}
    job_by_id = {job["id"]: job for job in jobs}
    if len(job_by_id) != len(jobs):
        raise RuntimeError("duplicate job IDs in partition")
    progress_path = directory / "progress.json"
    previous_recorded = 0.0
    if resume and progress_path.exists():
        previous = json.loads(progress_path.read_text(encoding="utf-8"))
        if previous.get("configuration_id") != configuration_id:
            raise ValueError("progress snapshot differs from requested forest")
        previous_recorded = previous.get("total_recorded_coordinator_seconds", 0.0)

    def progress_snapshot():
        seconds = time.perf_counter() - started
        write_json(progress_path, {
            "format": "markov-parallel-progress", "schema_version": SCHEMA_VERSION,
            "configuration_id": configuration_id,
            "updated_utc": datetime.now(timezone.utc).isoformat(),
            "completed_job_ids": sorted(completed), "completed_jobs": len(completed),
            "total_jobs": len(jobs), "workers_requested": workers,
            "strict_triples_in_completed_jobs": sum(
                item["statistics"]["strict_triples"] for item in completed.values()),
            "strict_triples_in_prefix_and_completed_jobs": sum(bins),
            "counting_session_seconds": seconds,
            "total_recorded_coordinator_seconds": previous_recorded + seconds,
            "counts_definition": "prefix and completed jobs only; unfinished jobs are excluded",
            "completed": len(completed) == len(jobs),
        })

    def merge(value):
        job_id = value["job_id"]
        if job_id not in job_by_id or job_id in completed:
            raise RuntimeError(f"unknown or repeated completed job: {job_id}")
        validate_result(value, job_by_id[job_id], configuration_id, len(exponents), backend_name)
        for index, number in enumerate(value["bins"]):
            bins[index] += number
        completed[job_id] = value
        progress_snapshot()

    pending = []
    for job in jobs:
        saved = result_path(directory, job)
        if saved.exists():
            merge(load_result(saved, job, configuration_id, len(exponents), backend_name))
        else:
            pending.append(job)
    # Start the estimated largest jobs first, keeping the manifest's stable
    # identifiers and exact forest unchanged. Dynamic scheduling then avoids
    # leaving a large subtree until the end of the worker queue.
    pending_ids = {job["id"] for job in pending}
    pending.sort(key=lambda job: math.log(3 * job["root"][0]) *
                 math.log(3 * job["root"][1]))
    if len(pending_ids) != len(pending) or {job["id"] for job in pending} != pending_ids:
        raise RuntimeError("scheduling changed the pending job identities")
    progress_snapshot()
    print(f"Partition: {len(jobs)} disjoint jobs; {prefix_statistics['strict_triples']:,} "
          f"prefix nodes; {len(completed)} jobs already complete; {len(pending)} pending.", flush=True)
    worker_configuration = {
        "exponents": exponents, "backend": backend_name,
        "configuration_id": configuration_id, "checkpoint_directory": str(directory),
        "resume": resume, "checkpoint_seconds": checkpoint_seconds,
        "progress_every": progress_every,
    }
    if pending:
        worker_count = min(workers, len(pending))
        if worker_count == 1:
            initialize_worker(worker_configuration)
            for job in pending:
                merge(count_job(job))
        else:
            with multiprocessing.get_context("spawn").Pool(
                    worker_count, initializer=initialize_worker,
                    initargs=(worker_configuration,)) as pool:
                for value in pool.imap_unordered(count_job, pending, chunksize=1):
                    merge(value)
                    print(f"Completed {len(completed)}/{len(jobs)} jobs; "
                          f"{sum(bins):,} strict triples in prefix/completed jobs; "
                          f"wall time {time.perf_counter() - started:.1f}s.", flush=True)
    checked = prefix_statistics["strict_triples"] + sum(
        value["statistics"]["strict_triples"] for value in completed.values())
    pruned = prefix_statistics["pruned_children"] + sum(
        value["statistics"]["pruned_children"] for value in completed.values())
    if len(completed) != len(jobs) or sum(bins) != checked or pruned != checked + 1:
        raise RuntimeError("inconsistent merged forest diagnostics")
    elapsed = time.perf_counter() - started
    worker_statistics = {}
    for value in completed.values():
        pid = str(value["worker_pid"])
        entry = worker_statistics.setdefault(pid, {"jobs": 0, "strict_triples": 0,
                                                   "summed_task_seconds": 0.0})
        entry["jobs"] += 1
        entry["strict_triples"] += value["statistics"]["strict_triples"]
        entry["summed_task_seconds"] += value["statistics"]["counting_seconds"]
    statistics = {
        "backend": backend_name, "backend_version": backend_version,
        "strict_triples": checked, "triples_including_exceptions": checked + 2,
        "pruned_children": pruned, "completed": True,
        "products_avoided_by_bit_length_guard": prefix_statistics[
            "products_avoided_by_bit_length_guard"] + sum(
                value["statistics"]["products_avoided_by_bit_length_guard"]
                for value in completed.values()),
        "maximum_pending_stack_entries_per_task": max(
            (value["statistics"]["maximum_pending_stack_entries"]
             for value in completed.values()), default=0),
        "counting_seconds": elapsed, "counting_seconds_definition": "current coordinator session wall time",
        "previous_recorded_coordinator_seconds": previous_recorded,
        "total_recorded_coordinator_seconds": previous_recorded + elapsed,
        "workers_requested": workers, "multiprocessing_start_method": "spawn",
        "requested_tasks": target_tasks, "task_count": len(jobs),
        "prefix_strict_triples": prefix_statistics["strict_triples"],
        "partition_checksum": partition_id, "configuration_id": configuration_id,
        "checkpoint_directory": str(directory),
        "resumed": resume, "tasks_reused_from_completed_results": len(jobs) - len(pending),
        "worker_statistics_by_pid": worker_statistics,
        "task_statistics": [{"job_id": job["id"], "root": job["root"],
                             **completed[job["id"]]["statistics"]} for job in jobs],
    }
    progress_snapshot()
    return bins, statistics


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-exponent", type=plotting.positive_int, default=2000)
    parser.add_argument("--sample-step", type=plotting.positive_int, default=1)
    parser.add_argument("--workers", type=plotting.positive_int, default=4)
    parser.add_argument("--tasks", type=plotting.positive_int, default=64)
    parser.add_argument("--backend", choices=("auto", "gmpy2", "python"), default="auto")
    parser.add_argument("--output-prefix", type=Path)
    parser.add_argument("--checkpoint-dir", type=Path)
    parser.add_argument("--checkpoint-seconds", type=plotting.positive_float, default=300)
    parser.add_argument("--progress-every", type=plotting.non_negative_int, default=5_000_000)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--no-plot", action="store_true")
    args = parser.parse_args()
    exponents = list(range(1, args.max_exponent + 1, args.sample_step))
    if exponents[-1] != args.max_exponent:
        exponents.append(args.max_exponent)
    prefix = (args.output_prefix or Path(__file__).resolve().parent /
              f"markov-error-10e{args.max_exponent}").resolve()
    directory = args.checkpoint_dir or prefix.parent / f".{prefix.name}-checkpoints"
    prefix.parent.mkdir(parents=True, exist_ok=True)
    print(f"Counting exact Markov triples up to 10^{args.max_exponent}; "
          f"{len(exponents):,} samples; {args.workers} worker processes.", flush=True)
    try:
        bins, statistics = count_parallel(
            exponents, args.backend, args.workers, args.tasks, directory,
            resume=args.resume, checkpoint_seconds=args.checkpoint_seconds,
            progress_every=args.progress_every)
    except ValueError as error:
        parser.error(str(error))
    rows = plotting.make_rows(exponents, bins)
    csv_path = prefix.with_suffix(".csv")
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    normalized = plotting.normalized_errors(rows)
    metadata = {
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "maximum_cutoff": f"10^{args.max_exponent}", "sample_count": len(exponents),
        "sample_step": args.sample_step,
        "sampling_definition": "exact counts at the listed integer exponents k; x=10**k",
        "plot_interpolation": "straight lines connect samples; the continuous error function is not computed",
        "counting_definition": "positive Markov triples a <= b <= c <= x",
        "exceptional_triples_included": [[1, 1, 1], [1, 1, 2]],
        "uniqueness_checked": False, "cutoff_comparisons": "exact integer arithmetic",
        "partition_weight": "1/(ln(3a)*ln(3b)); floating point affects scheduling only",
        "constant": plotting.CONSTANT_TEXT, "constant_source": plotting.CONSTANT_SOURCE,
        "main_term": "C * (k * ln(10) + ln(3))**2 at x=10**k",
        "main_term_decimal_precision": plotting.DECIMAL_PRECISION,
        "normalization": "error / sqrt(k * ln(10))", "python_version": sys.version,
        **statistics,
        "last_sample": rows[-1],
        "minimum_sampled_error": min(rows, key=lambda row: Decimal(row["error"])),
        "maximum_sampled_error": max(rows, key=lambda row: Decimal(row["error"])),
        "maximum_absolute_normalized_error": str(max(value.copy_abs() for value in normalized)),
    }
    json_path = prefix.with_suffix(".json")
    write_json(json_path, metadata)
    print(f"Counted {statistics['strict_triples']:,} strict triples "
          f"({statistics['triples_including_exceptions']:,} including exceptions) "
          f"in {statistics['counting_seconds']:.3f} seconds this session.", flush=True)
    print(f"Final sampled error: {rows[-1]['error']}")
    print(csv_path)
    print(json_path)
    if not args.no_plot:
        for path in plotting.plot_rows(rows, prefix, mode="both"):
            print(path)


if __name__ == "__main__":
    main()
