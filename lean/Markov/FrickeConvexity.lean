import Markov.TraceRayLimit

/-! Strict lower supporting inequalities for Fricke trace lengths.
These estimates are unconditional real analysis and do not assume the
existence of an interpolating norm. -/

noncomputable section
attribute [-instance] DivisionRing.toRatAlgebra
local instance frickeConvexityRatRealAlgebra : Algebra ℚ ℝ := DivisionRing.toRatAlgebra

namespace Markov

/-- A positive pair with product greater than one has sum greater than two. -/
theorem positive_pair_sum_gt_two (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hp : 1 < x * y) : 2 < x + y := by
  by_contra h
  have hs : x + y ≤ 2 := le_of_not_gt h
  have hs0 : 0 ≤ x + y := by positivity
  have hsq : (x + y) ^ 2 ≤ 4 := by nlinarith
  nlinarith [sq_nonneg (x - y)]

/-- The length of `x+y` lies strictly above the logarithmic model `log x`
when the product of the two positive terms exceeds one. -/
theorem arcosh_half_add_gt_log (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hp : 1 < x * y) : Real.log x < Real.arcosh ((x + y) / 2) := by
  have hs : 2 < x + y := positive_pair_sum_gt_two x y hx hy hp
  by_cases hx1 : x ≤ 1
  · have hl : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
    have ha : 0 < Real.arcosh ((x + y) / 2) := Real.arcosh_pos (by linarith)
    linarith
  · have hx1' : 1 < x := lt_of_not_ge hx1
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1'.le
    have hi : x⁻¹ < y := by
      rw [← one_div]
      apply (div_lt_iff₀ hx).mpr
      nlinarith
    have hc : Real.cosh (Real.log x) < (x + y) / 2 := by
      rw [Real.cosh_log hx]
      linarith
    have ha := (Real.arcosh_lt_arcosh (Real.cosh_pos _)
      (show 0 < (x + y) / 2 by positivity)).mpr hc
    rw [Real.arcosh_cosh hlog] at ha
    exact ha

/-- Every point on a positive trace wave lies strictly above its limiting
logarithmic supporting line. No norm interpretation is assumed. -/
theorem traceWave_length_gt_log_model (r a a' : ℝ) (hr : 0 < r)
    (ha : 0 < a) (ha' : 0 < a') (hp : 1 < a * a') (n : ℕ) :
    2 * ((n : ℝ) * Real.log r + Real.log a) <
      2 * Real.arcosh (traceWave r a a' n / 2) := by
  have hx : 0 < a * r ^ n := mul_pos ha (pow_pos hr _)
  have hy : 0 < a' * (r⁻¹) ^ n := mul_pos ha' (pow_pos (inv_pos.mpr hr) _)
  have hprod : 1 < (a * r ^ n) * (a' * (r⁻¹) ^ n) := by
    rw [mul_mul_mul_comm, ← mul_pow, mul_inv_cancel₀ hr.ne', one_pow, mul_one]
    exact hp
  have hl := arcosh_half_add_gt_log _ _ hx hy hprod
  rw [Real.log_mul ha.ne' (pow_ne_zero _ hr.ne'), Real.log_pow] at hl
  dsimp [traceWave]
  linarith

/-- The two opposite-ray lengths exceed the total linear growth. The
strict corner comes from the coefficient product greater than one. -/
theorem traceWave_opposite_length_sum_gt (r a a' : ℝ) (hr : 0 < r)
    (ha : 0 < a) (ha' : 0 < a') (hp : 1 < a * a') (n m : ℕ) :
    2 * (((n : ℝ) + (m : ℝ)) * Real.log r) <
      2 * Real.arcosh (traceWave r a a' n / 2) +
        2 * Real.arcosh (traceWave r a' a m / 2) := by
  have hn := traceWave_length_gt_log_model r a a' hr ha ha' hp n
  have hm := traceWave_length_gt_log_model r a' a hr ha' ha (by simpa only [mul_comm] using hp) m
  have hlog : 0 < Real.log (a * a') := Real.log_pos hp
  rw [Real.log_mul ha.ne' ha'.ne'] at hlog
  linarith

/-- The opposite Fricke traces give an unconditional strict supporting
inequality, with the actual quadratic-field coefficients and norm. -/
theorem frickeRay_opposite_length_sum_gt (t b c : ℤ) [ht : Fact (3 ≤ t)]
    (hb : 0 < b) (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) (n m : ℕ) :
    2 * (((n : ℝ) + (m : ℝ)) * Real.log (positiveTraceRoot t)) <
      2 * Real.arcosh ((frickeRay t b c n : ℝ) / 2) +
        2 * Real.arcosh ((frickeRay t b (t * b - c) m : ℝ) / 2) := by
  have hp := traceCoefficient_real_pos t b c hb hf
  have hn : (1 : ℝ) < (Algebra.norm ℚ (traceCoefficient t b c) : ℝ) := by
    exact_mod_cast traceCoefficient_field_norm_gt_one t b c ht.out hf
  rw [traceField_real_norm_eq] at hn
  have hh := traceWave_opposite_length_sum_gt (positiveTraceRoot t)
    (traceRealEmbedding t (traceCoefficient t b c))
    (traceRealEmbedding t (star (traceCoefficient t b c)))
    (by linarith [positiveTraceRoot_gt_one t ht.out]) hp.1 hp.2 hn n m
  simpa only [frickeRay_eq_traceWave, ← traceCoefficient_star t b c ht.out, star_star] using hh

end Markov
