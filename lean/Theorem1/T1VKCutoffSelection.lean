import T1VKWeightGrowth
import T1RealCutoffSelection

/-! The cutoff driven by the Vinogradov–Korobov weight, including
admissibility and the square-root lower bound on its actual integer cutoff. -/
noncomputable section
open Filter Asymptotics
namespace Markov

def t1_vkY (c R : ℝ) : ℝ := Real.exp (c*t1_vkWeight R/4)

theorem t1_vkY_tendsto (c : ℝ) (hc : 0 < c) : Tendsto (t1_vkY c) atTop atTop := by
  have hp := t1_vkWeight_tendsto.const_mul_atTop (show 0 < c/4 by positivity)
  refine (Real.tendsto_exp_atTop.comp hp).congr fun R => ?_
  change Real.exp (c/4*t1_vkWeight R) = t1_vkY c R
  rw [t1_vkY,show c/4*t1_vkWeight R = c*t1_vkWeight R/4 by ring]

theorem t1_vkY_eventually_le_quarterPower (c : ℝ) (hc : 0 < c) :
    ∀ᶠ R : ℝ in atTop, t1_vkY c R ≤ R^((1 : ℝ)/4) := by
  have hsmall := t1_vkWeight_isLittleO_log.bound (c := 1/c) (by positivity)
  filter_upwards [hsmall,eventually_gt_atTop (Real.exp 1)] with R hsmallR hR
  have hR0 := (Real.exp_pos _).trans hR
  have hlog : 0 < Real.log R := by
    have h1 : 1 < R := by
      rw [← Real.exp_zero]
      exact (Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ)<1)).trans hR
    exact Real.log_pos h1
  have hW := t1_vkWeight_pos R hR
  have hW' : t1_vkWeight R ≤ Real.log R/c := calc
    _ ≤ (1/c)*Real.log R := by
      simpa only [Real.norm_eq_abs,abs_of_pos hW,abs_of_pos hlog] using hsmallR
    _ = _ := by ring
  rw [t1_vkY,Real.rpow_def_of_pos hR0]
  have hmul : t1_vkWeight R*c ≤ Real.log R := (le_div_iff₀ hc).1 hW'
  exact Real.exp_le_exp.mpr (by linarith)

theorem t1_vkCutoff_eventually_admissible (c : ℝ) (hc : 0 < c) (T : ℝ) (N : ℕ) :
    ∀ᶠ R : ℝ in atTop, T ≤ t1_vkY c R ∧ 4*t1_vkY c R ≤ R ∧
      R^((1 : ℝ)/2) ≤ (t1_realCutoff R (t1_vkY c R) : ℝ) ∧
      N ≤ t1_realCutoff R (t1_vkY c R) := by
  have hquarter := tendsto_rpow_atTop (show (0 : ℝ)<(1 : ℝ)/4 by norm_num)
  have hhalf := tendsto_rpow_atTop (show (0 : ℝ)<(1 : ℝ)/2 by norm_num)
  filter_upwards [(t1_vkY_tendsto c hc).eventually_ge_atTop T,
    t1_vkY_eventually_le_quarterPower c hc,hquarter.eventually_ge_atTop 2,
    hhalf.eventually_ge_atTop (max 2 (N : ℝ)),eventually_gt_atTop (0 : ℝ)]
    with R hT hY hq hh hR
  let Y := t1_vkY c R
  have hY0 : 0 < Y := Real.exp_pos _
  have hq2 : R^((1 : ℝ)/4)*R^((1 : ℝ)/4) = R^((1 : ℝ)/2) := by
    rw [← Real.rpow_add hR,show (1 : ℝ)/4+1/4 = 1/2 by norm_num]
  have hh2 : R^((1 : ℝ)/2)*R^((1 : ℝ)/2) = R := by
    rw [← Real.rpow_add hR,show (1 : ℝ)/2+1/2 = 1 by norm_num,Real.rpow_one]
  have hYh : 2*Y ≤ R^((1 : ℝ)/2) := calc
    _ ≤ 2*R^((1 : ℝ)/4) := mul_le_mul_of_nonneg_left hY (by norm_num)
    _ ≤ _ := by
      rw [← hq2]
      exact mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hR.le _)
  have hh' : 2 ≤ R^((1 : ℝ)/2) := (le_max_left _ _).trans hh
  have h4 : 4*Y ≤ R := calc
    _ = 2*(2*Y) := by ring
    _ ≤ 2*R^((1 : ℝ)/2) := mul_le_mul_of_nonneg_left hYh (by norm_num)
    _ ≤ R^((1 : ℝ)/2)*R^((1 : ℝ)/2) :=
      mul_le_mul_of_nonneg_right hh' (Real.rpow_nonneg hR.le _)
    _ = R := hh2
  have hd := (t1_realCutoff_bounds R Y hY0 ((le_div_iff₀ hY0).2 h4)).2.1
  have hhD : R^((1 : ℝ)/2) ≤ (t1_realCutoff R Y : ℝ) := by
    refine le_trans ((le_div_iff₀ (show 0 < 2*Y by positivity)).2 ?_) hd
    exact (mul_le_mul_of_nonneg_left hYh (Real.rpow_nonneg hR.le _)).trans_eq hh2
  refine ⟨hT,h4,hhD,?_⟩
  exact_mod_cast ((le_max_right (2 : ℝ) (N : ℝ)).trans hh).trans hhD

end Markov
