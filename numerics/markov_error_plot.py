#!/usr/bin/env python3
"""Count Markov triples once and plot the sampled error term.

M(x) counts positive solutions a <= b <= c <= x of
a*a + b*b + c*c = 3*a*b*c.  This counts triples, without testing whether
their largest coordinates are distinct.  The two exceptional triples
(1,1,1) and (1,1,2) are included in M(x).

Example (matplotlib is required unless --no-plot is given)::

    python markov_error_plot.py --max-exponent 2000 --backend gmpy2

Every cutoff comparison uses exact integers.  A floating-point estimate
only proposes a histogram bin, which exact comparisons then correct.
No Markov-number set, path codes, or uniqueness checks are retained.
"""

from __future__ import annotations

import argparse
import csv
from datetime import datetime, timezone
from decimal import Decimal, localcontext
from functools import lru_cache
import json
import math
import os
from pathlib import Path
import pickle
import sys
import tempfile
import time


CONSTANT_TEXT = "0.18071710471180647805779264904916762147630562767088273"
CONSTANT_SOURCE = "https://oeis.org/A261613"
DECIMAL_PRECISION = 70
LOG10_2 = math.log10(2)
CHECKPOINT_SCHEMA_VERSION = 1


def positive_int(text: str) -> int:
    value = int(text)
    if value < 1:
        raise argparse.ArgumentTypeError("must be a positive integer")
    return value


def non_negative_int(text: str) -> int:
    value = int(text)
    if value < 0:
        raise argparse.ArgumentTypeError("must be non-negative")
    return value


def positive_float(text: str) -> float:
    value = float(text)
    if not math.isfinite(value) or value <= 0:
        raise argparse.ArgumentTypeError("must be a positive finite number")
    return value


def select_backend(name: str):
    if name != "python":
        try:
            import gmpy2
        except ImportError:
            if name == "gmpy2":
                raise ValueError("gmpy2 is not installed; use --backend python")
        else:
            return gmpy2.mpz, "gmpy2", gmpy2.version()
    return int, "python", None


@lru_cache(maxsize=1)
def prepare_cutoffs(exponents: tuple[int, ...], backend: str):
    """Reuse exact powers and the bin map across subtree jobs in a process."""
    integer, backend_name, backend_version = select_backend(backend)
    cutoffs = tuple(integer(10) ** exponent for exponent in exponents)
    exponent_to_bin = [0] * (exponents[-1] + 1)
    previous = 0
    for index, exponent in enumerate(exponents):
        for k in range(previous + 1, exponent + 1):
            exponent_to_bin[k] = index
        previous = exponent
    return (integer, backend_name, backend_version, cutoffs,
            tuple(exponent_to_bin), cutoffs[-1].bit_length())


def _write_checkpoint(path: Path, state: dict) -> None:
    """Atomically replace a local checkpoint with exact integer state."""
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile("wb", dir=path.parent,
                                         prefix=f".{path.name}.", delete=False) as handle:
            temporary = Path(handle.name)
            pickle.dump(state, handle, protocol=pickle.HIGHEST_PROTOCOL)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def count_bins(exponents: list[int], backend: str = "auto", *,
               initial_stack: list[tuple] | None = None,
               checkpoint_path: Path | None = None, resume: bool = False,
               checkpoint_seconds: float = 300, progress_every: int = 5_000_000,
               progress_label: str = "count", stop_after: int | None = None):
    """Return exact disjoint-bin counts and traversal diagnostics.

    The Markov tree rooted at (1,2,5) has children
    (a,c,3*a*c-b) and (b,c,3*b*c-a).  Descent gives every strictly
    increasing positive Markov triple exactly once.  Both children have
    a larger maximum, so rejecting a child also rejects its descendants.

    A child 3*a*c-b is larger than 2*a*c, since b < c and a >= 1.
    If bit_length(a) + bit_length(c) > bit_length(bound), then
    2*a*c >= 2**bit_length(bound) > bound.  This cheaply rejects that
    child without performing its large multiplication.  The same
    argument applies to 3*b*c-a.  Remaining children are compared with
    the exact bound.

    initial_stack can contain disjoint subtree roots for parallel jobs;
    its bins do not include the two exceptional triples.  Checkpoints
    are trusted, locally created pickle files.  stop_after permits a
    controlled partial run for checkpoint validation; a partial result
    has completed=False and must not be treated as the full count.
    """
    if not exponents or exponents != sorted(set(exponents)) or exponents[0] < 1:
        raise ValueError("exponents must be a strictly increasing positive list")
    if progress_every < 0 or checkpoint_seconds <= 0 or not math.isfinite(checkpoint_seconds):
        raise ValueError("invalid progress or checkpoint interval")
    if stop_after is not None and (stop_after < 1 or checkpoint_path is None):
        raise ValueError("stop_after requires a positive count and checkpoint_path")
    if resume and checkpoint_path is None:
        raise ValueError("resume requires checkpoint_path")
    state = None
    if resume:
        with Path(checkpoint_path).open("rb") as handle:
            state = pickle.load(handle)
        if not isinstance(state, dict) or state.get("schema_version") != CHECKPOINT_SCHEMA_VERSION:
            raise ValueError("unsupported checkpoint schema")
        if state.get("format") != "markov-count-bins-checkpoint":
            raise ValueError("not a Markov counting checkpoint")
        if state["exponents"] != exponents:
            raise ValueError("checkpoint sampling exponents differ from requested exponents")
        if initial_stack is not None:
            requested_roots = [tuple(map(int, root)) for root in initial_stack]
            if requested_roots != state["initial_roots"]:
                raise ValueError("checkpoint initial roots differ from requested roots")
        if backend == "auto":
            backend = state["backend"]
        elif backend != state["backend"]:
            raise ValueError("checkpoint backend differs from requested backend")
    integer, backend_name, backend_version, cutoffs, exponent_to_bin, bound_bits = prepare_cutoffs(
        tuple(exponents), backend)
    if state is not None and backend_name != state["backend"]:
        raise ValueError("checkpoint backend differs from requested backend")
    bound = cutoffs[-1]
    if state is None:
        initial_roots = ([tuple(map(int, root)) for root in initial_stack]
                         if initial_stack is not None else [(1, 2, 5)])
        for a, b, c in initial_roots:
            if not (0 < a < b < c <= bound) or a*a + b*b + c*c != 3*a*b*c:
                raise ValueError("initial roots must be strict Markov triples below the bound")
        counts = [0] * len(exponents)
        stack = [tuple(map(integer, root)) for root in initial_roots]
        checked = pruned = guard_rejections = 0
        max_stack = len(stack)
        prior_elapsed = 0.0
    else:
        if state["cutoff"] != int(bound):
            raise ValueError("checkpoint cutoff differs from requested cutoff")
        initial_roots = state["initial_roots"]
        counts = state["counts"]
        if len(counts) != len(exponents) or any(not isinstance(n, int) or n < 0 for n in counts):
            raise ValueError("invalid checkpoint histogram")
        stack = [tuple(map(integer, root)) for root in state["stack"]]
        checked = state["checked"]
        pruned = state["pruned"]
        guard_rejections = state["guard_rejections"]
        max_stack = state["max_stack"]
        prior_elapsed = state["elapsed_seconds"]
        if sum(counts) != checked or pruned != checked + len(initial_roots) - len(stack):
            raise ValueError("inconsistent checkpoint counts or frontier")
    start = time.perf_counter()
    next_progress = ((checked // progress_every + 1) * progress_every
                     if progress_every else None)
    # Clock reads are amortized rather than performed at every tree node.
    clock_every = min(progress_every or 100_000, 100_000)
    next_clock_check = checked + clock_every
    next_checkpoint_time = start + checkpoint_seconds

    def save_checkpoint() -> None:
        _write_checkpoint(Path(checkpoint_path), {
            "format": "markov-count-bins-checkpoint",
            "schema_version": CHECKPOINT_SCHEMA_VERSION,
            "created_utc": datetime.now(timezone.utc).isoformat(),
            "exponents": exponents,
            "backend": backend_name,
            "backend_version": backend_version,
            "initial_roots": initial_roots,
            "cutoff": int(bound),
            "counts": list(counts),
            "stack": [tuple(map(int, root)) for root in stack],
            "checked": checked,
            "pruned": pruned,
            "guard_rejections": guard_rejections,
            "max_stack": max_stack,
            "elapsed_seconds": prior_elapsed + time.perf_counter() - start,
            "completed": not stack,
        })

    while stack:
        a, b, c = stack.pop()
        c_bits = c.bit_length()
        estimated_exponent = min(exponents[-1], int((c_bits - 1) * LOG10_2) + 1)
        index = exponent_to_bin[estimated_exponent]
        while c > cutoffs[index]:
            index += 1
        while index > 0 and c <= cutoffs[index - 1]:
            index -= 1
        counts[index] += 1
        checked += 1

        three_c = 3 * c
        if a.bit_length() + c_bits <= bound_bits:
            child_c = a * three_c - b
            if child_c <= bound:
                stack.append((a, c, child_c))
            else:
                pruned += 1
        else:
            pruned += 1
            guard_rejections += 1

        if b.bit_length() + c_bits <= bound_bits:
            child_c = b * three_c - a
            if child_c <= bound:
                stack.append((b, c, child_c))
            else:
                pruned += 1
        else:
            pruned += 1
            guard_rejections += 1
        if len(stack) > max_stack:
            max_stack = len(stack)

        if next_progress is not None and checked >= next_progress:
            elapsed = prior_elapsed + time.perf_counter() - start
            print(f"{progress_label}: {checked:,} triples; elapsed {elapsed:.1f}s; "
                  f"pending roots {len(stack):,}", file=sys.stderr, flush=True)
            next_progress += progress_every
        if checkpoint_path is not None and checked >= next_clock_check:
            now = time.perf_counter()
            if now >= next_checkpoint_time:
                save_checkpoint()
                print(f"{progress_label}: checkpoint saved after {checked:,} triples",
                      file=sys.stderr, flush=True)
                next_checkpoint_time = now + checkpoint_seconds
            next_clock_check = checked + clock_every
        if stop_after is not None and checked >= stop_after:
            break

    elapsed = prior_elapsed + time.perf_counter() - start
    if sum(counts) != checked or pruned != checked + len(initial_roots) - len(stack):
        raise RuntimeError("inconsistent traversal diagnostics")
    if checkpoint_path is not None:
        save_checkpoint()
    return counts, {
        "backend": backend_name,
        "backend_version": backend_version,
        "strict_triples": checked,
        "triples_including_exceptions": checked + (2 if initial_roots == [(1, 2, 5)] else 0),
        "initial_root_count": len(initial_roots),
        "completed": not stack,
        "pruned_children": pruned,
        "products_avoided_by_bit_length_guard": guard_rejections,
        "maximum_pending_stack_entries": max_stack,
        "counting_seconds": elapsed,
    }


def make_rows(exponents: list[int], bin_counts: list[int]) -> list[dict]:
    """Accumulate bins and subtract the main term at high precision."""
    rows = []
    cumulative = 2  # (1,1,1) and (1,1,2) lie below every sampled cutoff.
    with localcontext() as context:
        context.prec = DECIMAL_PRECISION
        constant = Decimal(CONSTANT_TEXT)
        log10 = Decimal(10).ln()
        log3 = Decimal(3).ln()
        for k, number in zip(exponents, bin_counts, strict=True):
            cumulative += number
            main_term = constant * (Decimal(k) * log10 + log3) ** 2
            rows.append({
                "k": k,
                "x": f"10^{k}",
                "strict_triples": cumulative - 2,
                "M_x": cumulative,
                "main_term": str(main_term),
                "error": str(Decimal(cumulative) - main_term),
            })
    return rows


def normalized_errors(rows: list[dict]) -> list[Decimal]:
    """Return E(10**k) / sqrt(log(10**k)) at the stored precision."""
    with localcontext() as context:
        context.prec = DECIMAL_PRECISION
        log10 = Decimal(10).ln()
        return [Decimal(row["error"]) / (Decimal(int(row["k"])) * log10).sqrt()
                for row in rows]


def normalized_prefix(prefix: Path) -> Path:
    if prefix.name.startswith("markov-error-"):
        return prefix.with_name(prefix.name.replace("markov-error-", "markov-error-normalized-", 1))
    return prefix.with_name(prefix.name + "-normalized")


def plot_rows(rows: list[dict], prefix: Path, mode: str = "both") -> list[str]:
    if mode not in ("raw", "normalized", "both"):
        raise ValueError("plot mode must be raw, normalized, or both")
    try:
        cache_root = Path(tempfile.gettempdir())
        os.environ.setdefault("MPLCONFIGDIR", str(cache_root / "markov-matplotlib-cache"))
        os.environ.setdefault("XDG_CACHE_HOME", str(cache_root / "markov-plot-cache"))
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except ImportError as error:
        raise RuntimeError(
            "matplotlib is required for plotting. The CSV remains usable; "
            "use --no-plot for counting or --render-csv to plot it later."
        ) from error

    k = [int(row["k"]) for row in rows]
    errors = [float(row["error"]) for row in rows]
    plots = []
    if mode in ("raw", "both"):
        plots.append((False, errors, prefix))
    if mode in ("normalized", "both"):
        plots.append((True, [float(value) for value in normalized_errors(rows)],
                      normalized_prefix(prefix)))
    outputs = []
    with plt.rc_context({
        "font.size": 11,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "svg.fonttype": "none",
        "savefig.facecolor": "white",
    }):
        for normalized, values, output_prefix in plots:
            fig, ax = plt.subplots(figsize=(11, 4.9), layout="constrained")
            ax.axhline(0, color="#666666", linewidth=0.8, zorder=1)
            if normalized:
                for reference in (-1, 1):
                    ax.axhline(reference, color="#999999", linewidth=0.8,
                               linestyle="--", zorder=1)
            ax.plot(k, values, color="#215c93", linewidth=0.85, zorder=2)
            ax.set_xlim(0, k[-1])
            ax.set_xlabel(r"$k=\log_{10}x$  (sampled at $x=10^k$)")
            if normalized:
                ax.set_ylabel(r"$\dfrac{M(10^k)-C\,(\log(3\cdot10^k))^2}{\sqrt{k\log 10}}$")
                ax.set_title("Markov counting error on the square-root logarithmic scale", pad=12)
                caption = ("Natural logarithms; the two exceptional triples are included. "
                           "Dashed lines mark ±1.")
            else:
                ax.set_ylabel(r"$M(10^k)-C\,(\log(3\cdot10^k))^2$")
                ax.set_title(rf"Markov triple counting error, $1\leq k\leq {k[-1]:,}$", pad=12)
                caption = (r"$M$ includes $(1,1,1)$ and $(1,1,2)$; "
                           r"$C=0.180717104711806478\ldots$; $\log$ is natural.")
            # Matplotlib chooses limits from all data and the reference lines;
            # the normalized plot never assumes the error remains below 1.
            ax.grid(axis="y", color="#dddddd", linewidth=0.5, alpha=0.8)
            ax.text(
                1, -0.20,
                caption + "\nLines connect samples; values between the sampled cutoffs are not shown.",
                transform=ax.transAxes, ha="right", va="top", fontsize=9,
                color="#555555",
            )
            for extension in ("png", "svg"):
                path = output_prefix.with_suffix(f".{extension}")
                fig.savefig(path, dpi=180, bbox_inches="tight")
                outputs.append(str(path.resolve()))
            plt.close(fig)
    return outputs


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-exponent", type=positive_int, default=2000,
                        help="largest cutoff is 10^K (default: 2000)")
    parser.add_argument("--sample-step", type=positive_int, default=1,
                        help="spacing of sampled integer exponents (default: 1)")
    parser.add_argument("--backend", choices=("auto", "gmpy2", "python"), default="auto")
    parser.add_argument("--output-prefix", type=Path,
                        help="output path without extension; default alongside script")
    parser.add_argument("--no-plot", action="store_true", help="write CSV/JSON only")
    parser.add_argument("--plot-mode", choices=("both", "raw", "normalized"), default="both",
                        help="plots to render (default: both)")
    parser.add_argument("--progress-every", type=non_negative_int, default=5_000_000,
                        help="report after this many further nodes; 0 disables progress")
    parser.add_argument("--checkpoint", type=Path,
                        help="path for an atomic local counting checkpoint")
    parser.add_argument("--checkpoint-seconds", type=positive_float, default=300,
                        help="checkpoint interval in seconds (default: 300)")
    parser.add_argument("--resume", action="store_true",
                        help="resume the trusted, self-created file given by --checkpoint")
    parser.add_argument("--render-csv", type=Path,
                        help="render an existing CSV without rerunning the count")
    args = parser.parse_args()
    if args.render_csv:
        with args.render_csv.open(newline="", encoding="utf-8") as handle:
            rows = list(csv.DictReader(handle))
        if not rows:
            parser.error("the CSV contains no samples")
        prefix = args.output_prefix or args.render_csv.with_suffix("")
        prefix.parent.mkdir(parents=True, exist_ok=True)
        for path in plot_rows(rows, prefix, args.plot_mode):
            print(path)
        return

    exponents = list(range(1, args.max_exponent + 1, args.sample_step))
    if exponents[-1] != args.max_exponent:
        exponents.append(args.max_exponent)
    prefix = args.output_prefix or Path(__file__).resolve().parent / f"markov-error-10e{args.max_exponent}"
    prefix.parent.mkdir(parents=True, exist_ok=True)
    print(f"Counting exact Markov triples up to 10^{args.max_exponent}; "
          f"{len(exponents):,} sampled cutoffs.", flush=True)
    try:
        bins, statistics = count_bins(
            exponents, args.backend, checkpoint_path=args.checkpoint, resume=args.resume,
            checkpoint_seconds=args.checkpoint_seconds, progress_every=args.progress_every)
    except (ValueError, OSError, pickle.UnpicklingError, EOFError) as error:
        parser.error(str(error))
    if not statistics["completed"]:
        raise RuntimeError("a partial count cannot be exported as a complete plot")
    rows = make_rows(exponents, bins)
    csv_path = prefix.with_suffix(".csv")
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    metadata = {
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "maximum_cutoff": f"10^{args.max_exponent}",
        "sample_count": len(exponents),
        "sample_step": args.sample_step,
        "sampling_definition": "exact counts at the listed integer exponents k; x=10**k",
        "plot_interpolation": "straight lines connect samples; the continuous error function is not computed",
        "counting_definition": "positive Markov triples a <= b <= c <= x",
        "exceptional_triples_included": [[1, 1, 1], [1, 1, 2]],
        "uniqueness_checked": False,
        "cutoff_comparisons": "exact integer arithmetic",
        "constant": CONSTANT_TEXT,
        "constant_source": CONSTANT_SOURCE,
        "main_term": "C * (k * ln(10) + ln(3))**2 at x=10**k",
        "main_term_decimal_precision": DECIMAL_PRECISION,
        "normalization": "error / sqrt(k * ln(10)) = error / sqrt(ln(x))",
        "python_version": sys.version,
        **statistics,
        "last_sample": rows[-1],
        "minimum_sampled_error": min(rows, key=lambda row: Decimal(row["error"])),
        "maximum_sampled_error": max(rows, key=lambda row: Decimal(row["error"])),
    }
    normalized = normalized_errors(rows)
    min_index = min(range(len(rows)), key=normalized.__getitem__)
    max_index = max(range(len(rows)), key=normalized.__getitem__)
    metadata.update({
        "last_sample_normalized_error": str(normalized[-1]),
        "minimum_sampled_normalized_error": {"k": rows[min_index]["k"],
                                              "normalized_error": str(normalized[min_index])},
        "maximum_sampled_normalized_error": {"k": rows[max_index]["k"],
                                              "normalized_error": str(normalized[max_index])},
    })
    json_path = prefix.with_suffix(".json")
    json_path.write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
    print(f"Counted {statistics['strict_triples']:,} strict triples "
          f"({statistics['triples_including_exceptions']:,} including exceptions) "
          f"in {statistics['counting_seconds']:.3f} seconds.", flush=True)
    print(f"Final sampled error: {rows[-1]['error']}")
    print(csv_path.resolve())
    print(json_path.resolve())
    if not args.no_plot:
        for path in plot_rows(rows, prefix, args.plot_mode):
            print(path)


if __name__ == "__main__":
    main()
