import Markov.TraceLengthBounds
import Mathlib.Analysis.SpecificLimits.Basic

/-! The Fricke recurrence along an integral ray, with the actual two
coefficients of Proposition 4 and the expanding real embedding. The geometric
identification of the recurrence with torus traces remains a separate input. -/

noncomputable section
attribute [-instance] DivisionRing.toRatAlgebra
local instance frickeRayRatRealAlgebra : Algebra ℚ ℝ := DivisionRing.toRatAlgebra
open Filter
open scoped Topology

namespace Markov

/-- Integer trace recurrence with initial values `b,c`. -/
def frickeRay (t b c : ℤ) : ℕ → ℤ
  | 0 => b
  | 1 => c
  | n + 2 => t * frickeRay t b c (n + 1) - frickeRay t b c n

/-- Two exponential solutions of the characteristic equation. -/
def traceWave (r a a' : ℝ) (n : ℕ) : ℝ := a * r ^ n + a' * (r⁻¹) ^ n

theorem traceWave_recurrence (r a a' t : ℝ) (hr : r ≠ 0) (ht : r + r⁻¹ = t)
    (n : ℕ) : traceWave r a a' (n + 2) =
      t * traceWave r a a' (n + 1) - traceWave r a a' n := by
  have hunit : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have he : r ^ 2 - t * r + 1 = 0 := by rw [← ht]; nlinarith [hunit]
  have he' : (r⁻¹) ^ 2 - t * r⁻¹ + 1 = 0 := by rw [← ht]; nlinarith [hunit]
  simp only [traceWave, pow_succ]
  linear_combination a * r ^ n * he + a' * (r⁻¹) ^ n * he'

theorem traceCoefficient_real_first (t b c : ℤ) [ht : Fact (3 ≤ t)] :
    traceRealEmbedding t (traceCoefficient t b c) * positiveTraceRoot t +
      traceRealEmbedding t (star (traceCoefficient t b c)) * (positiveTraceRoot t)⁻¹ =
        (c : ℝ) := by
  have hs := congrArg (traceRealEmbedding t) (traceCoefficient_add_star t b c ht.out)
  have hd := congrArg (traceRealEmbedding t) (traceCoefficient_mul_denominator t b c ht.out)
  simp only [map_add, map_intCast] at hs
  simp only [map_mul, map_sub, map_intCast, traceRoot_star_eq_inv, map_inv₀,
    traceRealEmbedding_root] at hd
  linear_combination hd + (positiveTraceRoot t)⁻¹ * hs

/-- The exact closed form of the integer Fricke recurrence. -/
theorem frickeRay_eq_traceWave (t b c : ℤ) [ht : Fact (3 ≤ t)] (n : ℕ) :
    (frickeRay t b c n : ℝ) = traceWave (positiveTraceRoot t)
      (traceRealEmbedding t (traceCoefficient t b c))
      (traceRealEmbedding t (star (traceCoefficient t b c))) n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    have hs := congrArg (traceRealEmbedding t) (traceCoefficient_add_star t b c ht.out)
    simpa [frickeRay, traceWave] using hs.symm
  | one => simpa [frickeRay, traceWave] using (traceCoefficient_real_first t b c).symm
  | more n hn hn1 =>
    rw [frickeRay]
    push_cast
    rw [hn, hn1, traceWave_recurrence _ _ _ _
      (by linarith [positiveTraceRoot_gt_one t ht.out]) (positiveTraceRoot_add_inv t ht.out)]

theorem traceWave_div_pow (r a a' : ℝ) (hr : r ≠ 0) (n : ℕ) :
    traceWave r a a' n / r ^ n = a + a' * (r⁻¹ * r⁻¹) ^ n := by
  rw [traceWave, mul_pow, inv_pow]
  field_simp

/-- The decaying conjugate term disappears after division by the expanding power. -/
theorem traceWave_normalized_limit (r a a' : ℝ) (hr : 1 < r) :
    Tendsto (fun n : ℕ => traceWave r a a' n / r ^ n) atTop (𝓝 a) := by
  have hri : 0 < r⁻¹ := inv_pos.mpr (by linarith)
  have hri1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have hq : r⁻¹ * r⁻¹ < 1 := by nlinarith
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg hri.le hri.le) hq
  have hh := (tendsto_const_nhds (x := a)).add (h.const_mul a')
  simpa only [mul_zero, add_zero, ← traceWave_div_pow r a a' (by linarith : r ≠ 0)] using hh

end Markov
