# Counting Markov triples and simple geodesics

Companion repository to Morten S. Risager's
[*Counting Markov triples and simple geodesics*](https://arxiv.org/abs/2610.36069v1).
The theorem numbering and saved figure follow arXiv version 1.

## Lean verification

The [Lean project](lean/README.md) contains formal proofs of both theorems.

| Result | Final Lean declaration |
| --- | --- |
| Theorem 1. The unconditional and quasi-Riemann-hypothesis asymptotics for the count of sorted positive Markov triples | [`Markov.t1_mainTheorem`](lean/Theorem1/T1ExactTheoremOne.lean#L15) |
| Theorem 12. The lattice-point asymptotic for the geometric norm on the modular once-punctured torus | [`Markov.modularMcShaneRivin_lattice_asymptotic`](lean/Markov/IntrinsicMcShaneRivinCount.lean#L156) |

To check the source snapshot from the repository root, run
`python3 lean/scripts/verify.py --check-only`. For a full verification,
install [elan](https://github.com/leanprover/elan#installation), then run:

```sh
cd lean
lake exe cache get
python3 scripts/verify.py
```

The project pins Lean 4.28.0 and mathlib. The
[verification record](lean/docs/VERIFICATION.md) describes the original
checks, the axiom audit, and the rebuild procedure.

## Numerical experiments

The [numerics guide](numerics/README.md) gives installation instructions,
quick tests, and commands for reproducing the full runs.

- The [count data](numerics/markov-error-10e30000.csv) give the exact count
  at each `x = 10^k` for `1 ≤ k ≤ 30,000`. The included
  [normalized-error PDF](numerics/markov-error-normalized-10e30000.pdf) is
  the figure submitted with arXiv v1.
- The [Frobenius run report](numerics/frobenius-10e30000.txt) records a
  finite check of all **862,356,773** triples through `10^30000`. The run
  found no repeated largest-coordinate residues modulo `2^128`, which
  implies distinct largest coordinates within that cutoff.
- The [unit-ball area program](numerics/unit_ball_volume.py) reproduces
  the saved [intervals for the area and leading constant](numerics/unit-ball-volume.txt)
  from the paper's Appendix A.

The large-run reports and sorting summaries are included. The packed
records and restart files are generated locally when running the programs.
The GitHub workflows check the Lean certificate and run the small
numerical examples.

## Citation and license

Please cite Morten S. Risager, *Counting Markov triples and simple
geodesics*, arXiv:2610.36069v1. Include the repository commit when
citing a particular software or data revision.

The Lean certificate is distributed under [Apache 2.0](lean/LICENSE).
The bundled zeta proof retains its [upstream license and attribution](lean/docs/DEPENDENCIES.md#vinogradovkorobov-source-port).
The numerical materials are provided as companions to the paper. A
separate reuse license for those materials has not been specified.
