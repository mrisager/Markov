# Theorem 12: statement and proof guide

Reference: Morten S. Risager, *Counting Markov triples and simple geodesics*,
[arXiv:2610.36069v1](https://arxiv.org/abs/2610.36069v1), Theorem 12.
The manuscript's label is `thm:lattice_count`.

## Final Lean statement

In `Markov/IntrinsicMcShaneRivinCount.lean`:

```lean
theorem modularMcShaneRivin_lattice_asymptotic :
    (fun R : ℝ => (modularMcShaneRivinLatticeCount R : ℝ) -
      (volume modularMcShaneRivinBall).toReal * R^2) =O[atTop]
      (fun R : ℝ => R / Real.log R ^ (3/2 : ℝ))
```

The namespace is `Markov`. The fractional exponent is real, not integer
division. The filter is `atTop`, so this is an asymptotic as real `R` tends to
positive infinity. The final theorem has no additional geometric-agreement,
classification, norm-existence, or area-identification hypothesis.

## Meaning of the definitions

| Formal definition | Mathematical role |
| --- | --- |
| `ModularTraceQuotient` | Actual quotient surface for the modular punctured torus |
| `modularTraceFixedSingularH1Equiv` | Genuine integral singular H1 in the original fixed positive A/B coordinates |
| `modularSimpleGeodesicLengthSet` | Periods of actual admissible embedded, locally unit-speed metric circles with prescribed H1 |
| `modularSimpleGeodesicLengthInf` | Infimum of that independently defined geometric length set |
| `IsModularIntrinsicNormExtension` | Continuous norm axioms and agreement with actual signed primitive geometric length infima |
| `modularMcShaneRivinNorm` | Choice from the proved unique such extension |
| `modularMcShaneRivinBall` | Unit sublevel set of that intrinsic norm |
| `modularMarkedHomologyVector` | Genuine integral H1 mapped to the standard Euclidean plane |
| `modularMcShaneRivinLattice` | Range of that actual marked homology map |
| `modularMcShaneRivinLatticePointSet R` | All marked lattice points in `R • modularMcShaneRivinBall` |
| `modularMcShaneRivinLatticeCount R` | Cardinality of that set |
| `modularMcShaneRivinArea` | Standard Euclidean volume of the intrinsic unit ball, as a real number |

The lattice count includes zero, nonprimitive vectors, and both orientations.
It is not a count modulo sign, a primitive-only count, or a quotient by the
surface's isometry group. Nonprimitive norm values follow from homogeneity;
they are not defined by an infimum over an empty embedded-curve length set.

## Main proof stages

1. **Analytic estimate for the constructed trace ball.** Farey trace algebra,
   norm and boundary geometry, angular estimates, section sampling, Poisson
   summation, and signed primitive-ray summation lead to
   `trace_lattice_asymptotic` in `TraceLatticeAsymptotic.lean`.
2. **Actual modular surface and marking.** The quotient action, covering,
   punctured-torus topology, complete metric, fundamental group, and integral
   singular H1 realize the original A/B marking.
3. **Canonical primitive geometry.** Actual canonical simple closed geodesics
   exist for every signed primitive class, with metric periods equal to the
   constructed trace values.
4. **Arbitrary admissible primitive circles.** Actual full-real lifts and
   finite quadrilateral cuts produce proper arcs, genuine cyclic gluing,
   sorted endpoints, connected arc/edge pairings, and geometric packet order.
   Literal mechanical-word identities and canonical conjugacy or inverse
   comparisons identify actual periods. Equal H1 alone is not used to infer
   equality of nonabelian free classes.
5. **Intrinsic length and norm.**
   `PrimitiveSimpleGeodesicLengthAgreement.lean` proves the independently
   defined primitive length set is a singleton. `IntrinsicMcShaneRivinNorm.lean`
   proves existence and uniqueness of the continuous genuine norm extension.
   The trace norm supplies an existence witness only after geometric primitive
   agreement has been established.
6. **Final geometric transfer.** `IntrinsicMcShaneRivinCount.lean` proves the
   intrinsic ball equals the trace ball and the actual marked lattice equals
   the full standard integer lattice. It then transfers the analytic estimate
   with the unchanged standard Euclidean area.

Useful terminal files, in addition to the final count module:

- `PrimitiveAxisTraceNorm.lean`
- `PrimitiveSimpleGeodesicLengthAgreement.lean`
- `IntrinsicMcShaneRivinNorm.lean`
- `TraceLatticeAsymptotic.lean`
- `ModularH1Transport.lean`
- `Audit.lean`

## Scope

This proves the specified geometric Theorem 12 for this modular punctured
torus. It does not claim a general norm theorem for every punctured-torus
metric or arbitrary topological simple-class H1-to-pi1 injectivity.
The proof of Theorem 1 is documented [separately](THEOREM1.md).

The entire finalized registration is retained, including older target
definitions and conditional transfer lemmas. These are valid Lean definitions
or implications, not evidence that their hypotheses or other paper targets
have been proved. The final theorem above is the authoritative completed
statement. See `docs/VERIFICATION.md` for the source and comment revision record.
