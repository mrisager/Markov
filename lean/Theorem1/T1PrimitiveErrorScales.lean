import Markov.Statements
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Positivity and analytic comparisons for the paper's exact primitive
error scales. These are real-function facts, not Möbius cancellation. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace Markov

theorem t1_primitiveConditionalScale_pos (R : ℝ) (hR : 1 < R) :
    0 < primitiveConditionalScale R := by
  unfold primitiveConditionalScale
  exact div_pos (by linarith) (Real.rpow_pos_of_pos (Real.log_pos hR) _)

theorem t1_primitiveUnconditionalScale_pos (R : ℝ) (hR : Real.exp 1 < R) :
    0 < primitiveUnconditionalScale R := by
  have he1 : 1 < Real.exp 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num)
  have hR1 : 1 < R := he1.trans hR
  have hlog : 1 < Real.log R := by
    have hl := Real.log_lt_log (Real.exp_pos 1) hR
    simpa only [Real.log_exp] using hl
  unfold primitiveUnconditionalScale
  exact div_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos (Real.log_pos hlog) _))
    (Real.rpow_pos_of_pos (Real.log_pos hR1) _)

theorem t1_power_saving_isLittleO_primitiveConditional (δ : ℝ) (hδ : 0 < δ) :
    (fun R : ℝ => R^(1-δ/2)) =o[atTop] primitiveConditionalScale := by
  have hlim := (isLittleO_log_rpow_rpow_atTop ((1 : ℝ)/2)
    (show 0 < δ/2 by linarith)).tendsto_div_nhds_zero
  have hz : ∀ᶠ R : ℝ in atTop, primitiveConditionalScale R = 0 → R^(1-δ/2) = 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
    intro he
    exact ((t1_primitiveConditionalScale_pos R hR).ne' he).elim
  apply isLittleO_of_tendsto' hz
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
  have hR0 : 0 < R := by linarith
  have hp0 : R^(δ/2) ≠ 0 := (Real.rpow_pos_of_pos hR0 _).ne'
  have hl0 : (Real.log R)^((1 : ℝ)/2) ≠ 0 :=
    (Real.rpow_pos_of_pos (Real.log_pos hR) _).ne'
  rw [primitiveConditionalScale,Real.rpow_sub hR0,Real.rpow_one]
  field_simp
  rfl

end Markov
