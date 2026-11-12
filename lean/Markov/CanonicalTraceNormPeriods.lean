import Markov.TraceCompatibility
import Markov.PaperPrimitiveHolonomy

noncomputable section
namespace Markov

/-- Full signed-quadrant primitive interpolation of the already constructed
trace norm, recovered from its checked all-quadrant trace compatibility. -/
theorem norm_intVector_quadrant (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    ‖intVector traceBasis p‖ =
      primitiveSeedLength (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
        (quadrantCoordinates k p) hp := by
  have hmap : ∀ {u v : ℤ × ℤ} {M N : IntMatrixTwo},
      SeededFarey (1, 0) (0, 1) (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
        u v M N →
      SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
        (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
        (seededDirection (quadrantSeedDirections k).1 (quadrantSeedDirections k).2 u)
        (seededDirection (quadrantSeedDirections k).1 (quadrantSeedDirections k).2 v) M N := by
    intro u v M N h
    induction h with
    | seed =>
      simpa only [(seededDirection_zero_one (quadrantSeedDirections k).1
          (quadrantSeedDirections k).2).1,
        (seededDirection_zero_one (quadrantSeedDirections k).1
          (quadrantSeedDirections k).2).2] using
        (SeededFarey.seed (u0 := (quadrantSeedDirections k).1)
          (v0 := (quadrantSeedDirections k).2)
          (M0 := (quadrantSeedMatrices k).1) (N0 := (quadrantSeedMatrices k).2))
    | left _ ih => simpa only [seededDirection_add] using ih.left
    | right _ ih => simpa only [seededDirection_add] using ih.right
  have htrace : (primitiveSeedTrace (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
      (quadrantCoordinates k p) hp : ℝ) = 2*Real.cosh (‖intVector traceBasis p‖/2) := by
    rcases primitiveSeedMatrix_spec (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
        (quadrantCoordinates k p) hp with ⟨v, N, h⟩ | ⟨u, M, h⟩
    · simpa only [quadrantCoordinates_reconstruct] using
        (tracePlane_quadrantTraceLengthCompatible k (hmap h)).1
    · simpa only [quadrantCoordinates_reconstruct] using
        (tracePlane_quadrantTraceLengthCompatible k (hmap h)).2
  rw [primitiveSeedLength, htrace]
  have hn : 0 ≤ ‖intVector traceBasis p‖/2 := by positivity
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.arcosh_cosh hn]
  ring

/-- The genuine canonical metric period equals the already constructed trace
norm of its original signed lattice label. -/
theorem paperPrimitiveHolonomy_period_eq_trace_norm (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp) =
      ‖intVector traceBasis p‖ := by
  rw [paperPrimitiveHolonomy_period, norm_intVector_quadrant k p hp]

/-- Actual one-period metric variation of the canonical curve, expressed in
the constructed trace-norm normalization for every signed quadrant. -/
theorem paperPrimitiveClosedGeodesic_trace_norm_variation (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    (eVariationOn (paperPrimitiveClosedGeodesic k p hp)
      (Set.Icc 0 ‖intVector traceBasis p‖)).toReal = ‖intVector traceBasis p‖ := by
  rw [← paperPrimitiveHolonomy_period_eq_trace_norm k p hp]
  exact modularClosedGeodesic_period_length (paperPrimitiveHolonomy k p hp)
    (paperPrimitiveHolonomy_hyperbolic k p hp)

end Markov
