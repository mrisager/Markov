import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! A uniform power majorant for the logarithmic counting bound in
Lemma 7. The quarter-power bound is used in the subsequent summation by
parts; its constant is independent of every cutoff parameter. -/

namespace Markov

/-- A logarithmic square is bounded by a fixed quarter power on [1,∞). -/
theorem log_two_mul_sq_le_quarter_power (T : ℝ) (hT : 1 ≤ T) :
    Real.log (2 * T) ^ 2 ≤ 128 * T ^ ((1 : ℝ) / 4) := by
  have hT0 : 0 ≤ T := by linarith
  have h2T : 0 ≤ 2 * T := by positivity
  have hlog0 : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  have hlog := Real.log_le_rpow_div h2T (show (0 : ℝ) < 1 / 8 by norm_num)
  have hlog' : Real.log (2 * T) ≤ 8 * (2 * T) ^ ((1 : ℝ) / 8) := by
    nlinarith only [hlog]
  have hsquare : Real.log (2 * T) ^ 2 ≤
      64 * ((2 * T) ^ ((1 : ℝ) / 8)) ^ 2 := by
    nlinarith [Real.rpow_nonneg h2T ((1 : ℝ) / 8)]
  have hpow : ((2 * T) ^ ((1 : ℝ) / 8)) ^ 2 =
      (2 * T) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_mul_natCast h2T]
    norm_num
  have htwo : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
    calc
      (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  calc
    Real.log (2 * T) ^ 2 ≤ 64 * (2 * T) ^ ((1 : ℝ) / 4) := by
      simpa only [hpow] using hsquare
    _ = 64 * (2 ^ ((1 : ℝ) / 4) * T ^ ((1 : ℝ) / 4)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hT0]
    _ ≤ 64 * (2 * T ^ ((1 : ℝ) / 4)) := by
      gcongr
    _ = 128 * T ^ ((1 : ℝ) / 4) := by ring

/-- The count bound softens to a uniform quarter-power majorant. -/
theorem le_quarter_power_of_le_log_square (N C T : ℝ)
    (hC : 0 ≤ C) (hT : 1 ≤ T) (hN : N ≤ C * Real.log (2 * T) ^ 2) :
    N ≤ (128 * C) * T ^ ((1 : ℝ) / 4) := by
  calc
    N ≤ C * Real.log (2 * T) ^ 2 := hN
    _ ≤ C * (128 * T ^ ((1 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left (log_two_mul_sq_le_quarter_power T hT) hC
    _ = _ := by ring

end Markov
