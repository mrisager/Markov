import Markov.FrickeRay

/-! Length asymptotics for the Fricke ray. These are real-analysis statements;
no hyperbolic surface or norm/trace identification is postulated here. -/

noncomputable section
open Filter
open scoped Topology

namespace Markov

/-- Exact correction between half the trace length and its logarithmic model. -/
theorem arcosh_half_eq_log_add (T : ℝ) (hT : 0 < T) :
    Real.arcosh (T / 2) = Real.log T +
      Real.log ((1 + Real.sqrt (1 - 4 / T ^ 2)) / 2) := by
  have hs : (T / 2) ^ 2 - 1 = (T / 2) ^ 2 * (1 - 4 / T ^ 2) := by
    field_simp
    ring
  have hroot : Real.sqrt ((T / 2) ^ 2 - 1) =
      (T / 2) * Real.sqrt (1 - 4 / T ^ 2) := by
    rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hcorr : 0 < (1 + Real.sqrt (1 - 4 / T ^ 2)) / 2 := by positivity
  rw [Real.arcosh, hroot, ← Real.log_mul hT.ne' hcorr.ne']
  congr 1
  ring

/-- The difference between `arcosh(T/2)` and `log T` vanishes as T grows. -/
theorem arcosh_half_sub_log_limit :
    Tendsto (fun T : ℝ => Real.arcosh (T / 2) - Real.log T) atTop (𝓝 0) := by
  have hi : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hsq := hi.pow 2
  have harg : Tendsto (fun T : ℝ => 1 - 4 / T ^ 2) atTop (𝓝 1) := by
    simpa [div_eq_mul_inv, inv_pow] using
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul hsq))
  have hroot := harg.sqrt
  have hcorr : Tendsto (fun T : ℝ => (1 + Real.sqrt (1 - 4 / T ^ 2)) / 2)
      atTop (𝓝 1) := by
    convert (tendsto_const_nhds.add hroot).div_const 2 using 1
    norm_num
  have hlog : Tendsto (fun T : ℝ => Real.log ((1 + Real.sqrt (1 - 4 / T ^ 2)) / 2))
      atTop (𝓝 0) := by simpa only [Real.log_one] using hcorr.log (by norm_num : (1 : ℝ) ≠ 0)
  apply hlog.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [arcosh_half_eq_log_add T hT]
  simp

/-- Positive wave coefficients force the Fricke trace to diverge to infinity. -/
theorem traceWave_tendsto_atTop (r a a' : ℝ) (hr : 1 < r) (ha : 0 < a)
    (ha' : 0 ≤ a') : Tendsto (traceWave r a a') atTop atTop := by
  have hp := (tendsto_pow_atTop_atTop_of_one_lt hr).const_mul_atTop ha
  apply tendsto_atTop_mono (fun n => ?_) hp
  dsimp [traceWave]
  have h : 0 ≤ a' * (r⁻¹) ^ n := by positivity
  linarith

/-- The logarithm of the trace has the expanding-root asymptotic. -/
theorem traceWave_log_limit (r a a' : ℝ) (hr : 1 < r) (ha : 0 < a)
    (ha' : 0 ≤ a') :
    Tendsto (fun n : ℕ => Real.log (traceWave r a a' n) - (n : ℝ) * Real.log r)
      atTop (𝓝 (Real.log a)) := by
  have h := (traceWave_normalized_limit r a a' hr).log ha.ne'
  convert h using 1
  ext n
  have hr0 : 0 < r := by linarith
  have hW : 0 < traceWave r a a' n := by
    dsimp [traceWave]
    exact add_pos_of_pos_of_nonneg (mul_pos ha (pow_pos hr0 _)) (by positivity)
  rw [Real.log_div hW.ne' (pow_ne_zero _ hr0.ne'), Real.log_pow]

/-- The length asymptotic used in the supporting-functional calculation. -/
theorem traceWave_length_limit (r a a' : ℝ) (hr : 1 < r) (ha : 0 < a)
    (ha' : 0 ≤ a') :
    Tendsto (fun n : ℕ => 2 * Real.arcosh (traceWave r a a' n / 2) -
      2 * (n : ℝ) * Real.log r) atTop (𝓝 (2 * Real.log a)) := by
  have hc := arcosh_half_sub_log_limit.comp (traceWave_tendsto_atTop r a a' hr ha ha')
  have hl := traceWave_log_limit r a a' hr ha ha'
  convert (hc.add hl).const_mul 2 using 1
  · ext n
    simp only [Function.comp_apply]
    ring
  · ring

/-- Recover a nonnegative length from its hyperbolic trace. -/
theorem length_eq_two_arcosh (T ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (htrace : T = 2 * Real.cosh (ℓ / 2)) : ℓ = 2 * Real.arcosh (T / 2) := by
  have hh : T / 2 = Real.cosh (ℓ / 2) := by linarith
  rw [hh, Real.arcosh_cosh (div_nonneg hℓ (by norm_num))]
  ring

/-- The actual integral traces have the asymptotic used in §3.1. -/
theorem frickeRay_length_limit (t b c : ℤ) [ht : Fact (3 ≤ t)]
    (hb : 0 < b) (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) :
    Tendsto (fun n : ℕ => 2 * Real.arcosh ((frickeRay t b c n : ℝ) / 2) -
      2 * (n : ℝ) * Real.log (positiveTraceRoot t)) atTop
      (𝓝 (2 * Real.log (traceRealEmbedding t (traceCoefficient t b c)))) := by
  have hp := traceCoefficient_real_pos t b c hb hf
  simpa only [frickeRay_eq_traceWave] using traceWave_length_limit
    (positiveTraceRoot t) (traceRealEmbedding t (traceCoefficient t b c))
    (traceRealEmbedding t (star (traceCoefficient t b c)))
    (positiveTraceRoot_gt_one t ht.out) hp.1 hp.2.le

end Markov
