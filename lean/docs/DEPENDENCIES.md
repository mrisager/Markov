# Dependencies and foundations

## Pinned software

- Lean `leanprover/lean4:v4.28.0`.
- Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- Python 3.10 or later, standard library only, for the verification wrapper.
- Git and elan for obtaining the pinned toolchain and dependencies.

Mathlib is the only direct Lake dependency. `lake-manifest.json` pins its
supporting packages, `plausible`, `LeanSearchClient`, `importGraph`,
`proofwidgets`, `aesop`, `Qq`, `batteries`, and `Cli`.
The build does not require a separate Prime Number Theorem project.

## Vinogradov–Korobov source port

Theorem 1 uses mathlib's Riemann zeta function and its nonvanishing for Re(s) ≥ 1. The wider high-height Vinogradov–Korobov region
comes from a port of David Sanftenberg's RiemannGaussian development at
revision `f5fd3ddb407972f9ca65298fbe9be3225fe06635`. The local port retains
the moment and Dirichlet block estimates, trims unrelated imports, and
connects them to checked Chebyshev, Blaschke, and zeta log-derivative
arguments. All **199** retained modules were checked on the same Lean and
mathlib pins as the rest of this certificate.
[Upstream source](https://github.com/dbsanfte/RiemannGaussian/tree/f5fd3ddb407972f9ca65298fbe9be3225fe06635).

The port's Lean files are included under
[`Theorem1/RiemannGaussian/`](../Theorem1/RiemannGaussian).
The [upstream Apache 2.0 license](../LICENSES/RiemannGaussian-Apache-2.0.txt)
and original notices are retained. Adapted files carry a source comment
identifying the modification. The verifier compiles the port from source
along with the Markov proofs. The fixed strip in the conditional branch is
expressed as the paper's quasi-Riemann hypothesis.

## Axioms and trust

The public-name audit allows these standard Lean principles.

| Lean name | Principle |
| --- | --- |
| `propext` | Propositional extensionality |
| `Classical.choice` | Classical choice |
| `Quot.sound` | Quotient soundness |

Both final declarations use these three principles. The verifier rejects any
other axiom, including `sorryAx`. Lean checks the proofs in its dependent type
theory with classical foundations. The checking process relies on the Lean
kernel, the toolchain, and imported compiled dependencies. A ZFC translation
is outside the scope of this certificate.
[Theorem Proving in Lean 4, Axioms and Computation](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/).
