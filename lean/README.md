# Lean certificates for Theorems 1 and 12

This repository formalizes Theorems 1 and 12 of Morten S. Risager's
[*Counting Markov triples and simple geodesics*](https://arxiv.org/abs/2610.36069v1).
The statements follow version 1 of the paper.

| Result | Lean entry point |
| --- | --- |
| Theorem 1. Asymptotics for the number of sorted positive Markov triples, with both the unconditional and quasi-Riemann-hypothesis error terms | [`Markov.t1_mainTheorem`](Theorem1/T1ExactTheoremOne.lean#L15) |
| Theorem 12. Lattice-point asymptotics for the geometric norm on the modular once-punctured torus | [`Markov.modularMcShaneRivin_lattice_asymptotic`](Markov/IntrinsicMcShaneRivinCount.lean#L156) |

Theorem 1 uses the same positive constant 2 × area(B<sub>X</sub>) / π² in
both branches. Theorem 12 uses the actual simple-geodesic length norm,
the paper's original A/B integral homology marking, and standard Euclidean
area. Its lattice count includes zero, both signs, and nonprimitive points.
The statements and their proof routes are described in
[Theorem 1](docs/THEOREM1.md) and [Theorem 12](docs/THEOREM12.md).

## Reproduce the verification

Install Git, Python 3.10 or later, and Lean's
[elan version manager](https://github.com/leanprover/elan#installation).
Run these commands from the `lean/` directory on Linux or macOS.

```sh
python3 scripts/verify.py --check-only
lake exe cache get
python3 scripts/verify.py
```

The first command checks the source snapshot and recorded audits without
running Lean. The last command recompiles all **894 local Lean files**,
including the two roots and their audit modules, and checks **6,859 distinct
axiom reports**. A full run can take substantial time. On success it writes
`verification/run/SUCCESS.json`.

For offline verification with an existing installation of the exact pinned
dependencies, pass `--packages /path/to/project/.lake/packages` to the verifier.
This reuses the external library objects and still rebuilds the local sources.
An ordinary `lake build` also builds the combined library. The strict verifier
additionally checks source identity, installed dependency revisions, and axioms.

Lean is pinned to **4.28.0** and mathlib to
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The transitive revisions are pinned
in `lake-manifest.json`. Keep that file when reproducing this snapshot.
GitHub Actions is configured to perform the same strict check.

## Repository guide

| Path | Contents |
| --- | --- |
| [`Markov.lean`](Markov.lean) and `Markov/` | Original Theorem 12 root, proof, and audit |
| [`Theorem1/MarkovTheorem1.lean`](Theorem1/MarkovTheorem1.lean) | Combined root. Import it as `MarkovTheorem1` |
| `Theorem1/` | Theorem 1 proof, local zeta port, and audit batches |
| [`scripts/verify.py`](scripts/verify.py) | Strict compilation, source integrity, and axiom audit |
| [`docs/VERIFICATION.md`](docs/VERIFICATION.md) | Original verification dates and reproduction details |
| [`docs/DEPENDENCIES.md`](docs/DEPENDENCIES.md) | Dependencies, source provenance, and foundations |
| `verification/` | Source hashes, audited declarations, and historical reports |

The two proofs were checked in the development workspace. The export contains
**115,066 Lean source lines** across 894 files, including comments and blank
lines. Of these, **92,936** contain Lean code, including audits and root
imports. Both counts exclude mathlib, scripts, and separate documentation.
The audit allowlist contains only `propext`, `Classical.choice`, and
`Quot.sound`. The quasi-Riemann hypothesis appears as a premise of the
conditional statement.

## Provenance and licensing

The paper is by Morten S. Risager. The formalization was developed with
assistance from OpenAI Codex. The Vinogradov–Korobov proof includes a port of
David Sanftenberg's [RiemannGaussian](https://github.com/dbsanfte/RiemannGaussian/tree/f5fd3ddb407972f9ca65298fbe9be3225fe06635).
The port is included as Lean source under
[`Theorem1/RiemannGaussian/`](Theorem1/RiemannGaussian), with the upstream
[Apache 2.0 license](LICENSES/RiemannGaussian-Apache-2.0.txt) and adaptation
notices. Mathlib is the only direct Lake dependency.

The original certificate sources and repository documentation are licensed
under [Apache License 2.0](LICENSE). The RiemannGaussian port retains its
upstream license, attribution, and modification notices. The paper is
available from arXiv under its own publication terms.

See the [companion repository README](../README.md) for the numerical
experiments and repository-wide workflows.
