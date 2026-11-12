import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

/-! The height and spatial smoothing errors on the logarithmic scale
used in the final parameter choice. -/

noncomputable section
open Filter Asymptotics
namespace Markov

theorem logarithmic_height_error_eq (a : ℝ) (ha : 0 < a) (R : ℝ)
    (hlog : 0 < Real.log R) :
    R / ((Real.log R / a) * Real.sqrt (Real.log R / a)) =
      a ^ (3 / 2 : ℝ) * (R / (Real.log R) ^ (3 / 2 : ℝ)) := by
  have hm (x : ℝ) (hx : 0 < x) : x * Real.sqrt x = x ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hm _ (div_pos hlog ha), Real.div_rpow hlog.le ha.le, div_div_eq_mul_div]
  ring

theorem logarithmic_height_error_isBigO (a : ℝ) (ha : 0 < a) :
    (fun R : ℝ => R / ((Real.log R / a) * Real.sqrt (Real.log R / a))) =O[atTop]
      (fun R : ℝ => R / (Real.log R) ^ (3 / 2 : ℝ)) := by
  apply IsBigO.of_bound (a ^ (3 / 2 : ℝ))
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with R hlog
  rw [logarithmic_height_error_eq a ha R (by linarith), norm_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg ha.le _)]

theorem logarithmic_square_error_isBigO :
    (fun R : ℝ => R / (Real.log R) ^ (2 : ℕ)) =O[atTop]
      (fun R : ℝ => R / (Real.log R) ^ (3 / 2 : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with R hlog
  have hlogpos : 0 < Real.log R := by linarith
  have hpow : (Real.log R) ^ (3 / 2 : ℝ) ≤ (Real.log R) ^ (2 : ℕ) := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (3 / 2 : ℝ) ≤ 2)
  rw [one_mul, norm_div, norm_div, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hlogpos.le _)]
  exact div_le_div_of_nonneg_left (norm_nonneg R) (Real.rpow_pos_of_pos hlogpos _) hpow

end Markov
