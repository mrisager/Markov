import Markov.IntegerNorm

/-! The denominator-clearing step of Lemma 5, using exactly the powers of
`t²` and `Δ` from the paper, split according to the sign of the exponent. -/

noncomputable section
attribute [-instance] DivisionRing.toRatAlgebra
local instance : Algebra ℚ ℝ := DivisionRing.toRatAlgebra

namespace Markov

def traceClearingFactor (t n : ℤ) : ℤ :=
  match n with
  | .ofNat k => t ^ (2 * k)
  | .negSucc k => (t ^ 2 - 4) ^ (k + 1)

theorem traceClearingFactor_pos (t n : ℤ) (ht : 3 ≤ t) :
    0 < traceClearingFactor t n := by
  have hΔ : 0 < t ^ 2 - 4 := by nlinarith
  cases n <;> simp only [traceClearingFactor] <;> positivity

theorem traceCoefficient_ne_zero (t b c : ℤ) [ht : Fact (3 ≤ t)]
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) : traceCoefficient t b c ≠ 0 := by
  have hn := traceCoefficient_field_norm_gt_one t b c ht.out hf
  intro h
  rw [h, Algebra.norm_zero] at hn
  norm_num at hn

theorem traceCoefficient_scaled_inverse (t b c : ℤ) [ht : Fact (3 ≤ t)]
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) :
    (t : TraceField t) ^ 2 * (traceCoefficient t b c)⁻¹ =
      ((t ^ 2 - 4 : ℤ) : TraceField t) * star (traceCoefficient t b c) := by
  have hA := traceCoefficient_ne_zero t b c hf
  rw [← traceCoefficient_scaled_product t b c ht.out hf]
  field_simp [hA]

theorem traceCoefficient_scaled_inverse_isIntegral (t b c : ℤ) [ht : Fact (3 ≤ t)]
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) :
    IsIntegral ℤ ((t : TraceField t) ^ 2 * (traceCoefficient t b c)⁻¹) := by
  rw [traceCoefficient_scaled_inverse t b c hf, traceCoefficient_star t b c ht.out]
  exact scaled_traceCoefficient_isIntegral t b (t * b - c) ht.out

theorem cleared_coefficient_power_isIntegral (t b c : ℤ) [Fact (3 ≤ t)]
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) (n : ℤ) :
    IsIntegral ℤ ((traceClearingFactor t n : TraceField t) *
      traceCoefficient t b c ^ (-n)) := by
  cases n with
  | ofNat k =>
    have h := (traceCoefficient_scaled_inverse_isIntegral t b c hf).pow k
    convert h using 1
    simp [traceClearingFactor, mul_pow, pow_mul, zpow_neg, inv_pow]
  | negSucc k =>
    have h := (scaled_traceCoefficient_isIntegral t b c Fact.out).pow (k + 1)
    convert h using 1
    simp [traceClearingFactor, mul_pow, Int.negSucc_eq]
    left
    norm_cast

theorem cleared_beta_isIntegral (t b c : ℤ) [Fact (3 ≤ t)]
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) (m n : ℤ) :
    IsIntegral ℤ ((traceClearingFactor t n : TraceField t) *
      (traceRoot t ^ m * traceCoefficient t b c ^ (-n))) := by
  have h := (traceRoot_zpow_isIntegral t m).mul
    (cleared_coefficient_power_isIntegral t b c hf n)
  convert h using 1
  ring

theorem cleared_beta_sub_one_isIntegral (t b c : ℤ) [Fact (3 ≤ t)]
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) (m n : ℤ) :
    IsIntegral ℤ ((traceClearingFactor t n : TraceField t) *
      (traceRoot t ^ m * traceCoefficient t b c ^ (-n) - 1)) := by
  rw [mul_sub, mul_one]
  exact (cleared_beta_isIntegral t b c hf m n).sub isIntegral_algebraMap

/-- The actual integer-norm inequality in the paper's proof of Lemma 5. -/
theorem cleared_beta_norm_lower_bound (t b c : ℤ) [ht : Fact (3 ≤ t)]
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) (m n : ℤ)
    (hexp : m ≠ 0 ∨ n ≠ 0) :
    let β := traceRoot t ^ m * traceCoefficient t b c ^ (-n)
    1 ≤ (traceClearingFactor t n : ℝ) ^ 2 *
      |traceRealEmbedding t β - 1| * |traceRealEmbedding t (star β) - 1| := by
  dsimp
  let β := traceRoot t ^ m * traceCoefficient t b c ^ (-n)
  have hD := traceClearingFactor_pos t n ht.out
  have hz : (traceClearingFactor t n : TraceField t) * (β - 1) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast ne_of_gt hD)
      (sub_ne_zero.mpr (trace_beta_ne_one t b c hf m n hexp))
  have h := traceField_one_le_product_embeddings t
    ((traceClearingFactor t n : TraceField t) * (β - 1))
    (cleared_beta_sub_one_isIntegral t b c hf m n) hz
  simp only [map_mul, map_sub, map_intCast, map_one, star_mul, star_sub,
    star_intCast, star_one, abs_mul] at h
  have hD' : (0 : ℝ) ≤ traceClearingFactor t n := by exact_mod_cast hD.le
  rw [abs_of_nonneg hD'] at h
  convert h using 1
  ring

end Markov
