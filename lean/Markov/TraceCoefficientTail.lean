import Markov.CornerTailDeficit
import Markov.TraceLengthBounds

/-! The real deficit estimate applied to the actual expanding embedding
of the trace-field coefficient on the upper Fricke branch. -/

noncomputable section
attribute [-instance] DivisionRing.toRatAlgebra
local instance traceCoefficientTailRatRealAlgebra : Algebra ℚ ℝ := DivisionRing.toRatAlgebra

namespace Markov

/-- The upper Fricke branch selects the coefficient at least half the
companion trace. -/
theorem traceCoefficient_real_ge_half (t b c : ℤ) [ht : Fact (3 ≤ t)]
    (hupper : t * b ≤ 2 * c) :
    (b : ℝ) / 2 ≤ traceRealEmbedding t (traceCoefficient t b c) := by
  have hr := positiveTraceRoot_gt_one t ht.out
  have hi : (positiveTraceRoot t)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have hd : 0 < positiveTraceRoot t - (positiveTraceRoot t)⁻¹ := by linarith
  rw [traceCoefficient_real_quotient]
  apply (le_div_iff₀ hd).mpr
  have hupperR : (t : ℝ) * (b : ℝ) ≤ 2 * (c : ℝ) := by exact_mod_cast hupper
  have hs := congrArg (fun x : ℝ => x * (b : ℝ)) (positiveTraceRoot_add_inv t ht.out)
  nlinarith

/-- Actual upper-branch trace coefficients have an explicit exponentially
small length deficit, written here in terms of the two integer traces. -/
theorem traceCoefficient_logarithmic_deficit_bounds
    (t b c : ℤ) [ht : Fact (3 ≤ t)] (hb : 3 ≤ b)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) (hupper : t * b ≤ 2 * c) :
    0 ≤ 2 * Real.log (positiveTraceRoot b) -
      2 * Real.log (traceRealEmbedding t (traceCoefficient t b c)) ∧
    2 * Real.log (positiveTraceRoot b) -
      2 * Real.log (traceRealEmbedding t (traceCoefficient t b c)) ≤
        96 / ((t : ℝ) ^ 2 * (b : ℝ) ^ 2) := by
  have hbpos : 0 < b := by omega
  have hsum := congrArg (traceRealEmbedding t) (traceCoefficient_add_star t b c ht.out)
  simp only [map_add, map_intCast] at hsum
  have hprod : traceRealEmbedding t (traceCoefficient t b c) *
      traceRealEmbedding t (star (traceCoefficient t b c)) =
        (t : ℝ) ^ 2 / ((t : ℝ) ^ 2 - 4) := by
    rw [← traceField_real_norm_eq, traceCoefficient_field_norm t b c ht.out hf]
    push_cast
    rfl
  exact logarithmic_coefficient_deficit_bounds (t : ℝ) (b : ℝ)
    (traceRealEmbedding t (traceCoefficient t b c))
    (traceRealEmbedding t (star (traceCoefficient t b c))) (positiveTraceRoot b)
    (by exact_mod_cast ht.out) (by exact_mod_cast hb)
    (traceCoefficient_real_pos t b c hbpos hf).1 (positiveTraceRoot_gt_one b hb)
    hsum hprod (traceCoefficient_real_ge_half t b c hupper)
    (positiveTraceRoot_add_inv b hb)

end Markov
