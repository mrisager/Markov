#!/usr/bin/env python3
"""Render the paper's normalized-error figure from an existing count CSV.

No Markov triples are enumerated. Run from this directory, for example:
    python plot_normalized_for_paper.py --output results/normalized-error-paper.pdf

Matplotlib and a working LaTeX installation are required to typeset all labels.
"""

from __future__ import annotations

import argparse
import csv
import os
from pathlib import Path
import tempfile

import markov_error_plot as counting


def main() -> None:
    base = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path,
                        default=base / "markov-error-10e30000.csv")
    parser.add_argument("--output", type=Path,
                        default=base / "markov-error-normalized-10e30000.pdf")
    args = parser.parse_args()
    with args.input.open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    if not rows:
        parser.error("the input CSV has no samples")
    exponents = [int(row["k"]) for row in rows]
    if exponents[0] <= 0 or any(a >= b for a, b in zip(exponents, exponents[1:])):
        parser.error("sample exponents must be positive and strictly increasing")
    values = [float(value) for value in counting.normalized_errors(rows)]

    cache = Path(tempfile.gettempdir()) / "markov-matplotlib-cache"
    os.environ.setdefault("MPLCONFIGDIR", str(cache))
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.ticker import FuncFormatter, MaxNLocator

    with plt.rc_context({"font.family": "serif", "font.size": 10,
                         "font.serif": ["Computer Modern Roman"],
                         "text.usetex": True, "pdf.fonttype": 42,
                         "axes.linewidth": 0.7, "path.simplify": False}):
        figure, axes = plt.subplots(figsize=(6.3, 3.05))
        axes.plot(exponents, values, color="#2a82fa", linewidth=0.4, zorder=3)
        axes.axhline(0, color="0.25", linewidth=0.55, zorder=1)
        for level in (-1, 1):
            axes.axhline(level, color="0.5", linestyle=(0, (4, 3)),
                         linewidth=0.65, zorder=1)
        axes.set_xlim(0, exponents[-1])
        span = max(1.0, max(abs(value) for value in values))
        axes.set_ylim(-1.09 * span, 1.09 * span)
        axes.xaxis.set_major_locator(MaxNLocator(nbins=6, integer=True))
        axes.xaxis.set_major_formatter(
            FuncFormatter(lambda n, pos: f"${int(n):,}$".replace(",", r"\,")))
        axes.yaxis.set_major_formatter(
            FuncFormatter(lambda n, pos: f"${(0.0 if abs(n) < 1e-12 else n):.1f}$"))
        axes.set_xlabel(r"$k=\log_{10}x$")
        axes.set_ylabel(r"$\left(M(x)-C(\log(3x))^2\right)/\sqrt{\log x}$")
        axes.spines[["top", "right"]].set_visible(False)
        axes.tick_params(width=0.7, length=3)
        figure.subplots_adjust(left=0.12, right=0.985, bottom=0.18, top=0.975)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        figure.savefig(args.output, bbox_inches="tight", pad_inches=0.03)
        plt.close(figure)
    print(f"{args.output.resolve()} ({len(rows):,} samples; no recounting)")


if __name__ == "__main__":
    main()
