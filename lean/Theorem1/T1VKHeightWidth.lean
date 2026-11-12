import T1VKWeightGrowth
import T1QRHStrip

/-! The classical zero-free width, with a harmless positive shift
which keeps both logarithms positive at every real ordinate. -/
noncomputable section
open Filter
namespace Markov

def t1_vkHeightBase : ℝ := Real.exp (Real.exp 1)

def t1_vkHeightLog (t : ℝ) : ℝ := Real.log (|t|+t1_vkHeightBase)

def t1_vkHeightDenom (t : ℝ) : ℝ :=
  (t1_vkHeightLog t)^((2 : ℝ)/3)*(Real.log (t1_vkHeightLog t))^((1 : ℝ)/3)

def t1_vkHeightWidth (c t : ℝ) : ℝ := c/t1_vkHeightDenom t

theorem t1_vkHeightLog_ge (t : ℝ) : Real.exp 1 ≤ t1_vkHeightLog t := by
  rw [← Real.log_exp (Real.exp 1)]
  exact Real.log_le_log (Real.exp_pos _) (le_add_of_nonneg_left (abs_nonneg t))

theorem t1_vkHeightDoubleLog_ge (t : ℝ) : 1 ≤ Real.log (t1_vkHeightLog t) := by
  rw [← Real.log_exp (1 : ℝ)]
  exact Real.log_le_log (Real.exp_pos _) (t1_vkHeightLog_ge t)

theorem t1_vkHeightDenom_ge_one (t : ℝ) : 1 ≤ t1_vkHeightDenom t := by
  have h1 : 1 ≤ Real.exp 1 := calc
    1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr zero_le_one
  have hL := h1.trans (t1_vkHeightLog_ge t)
  have hLL := t1_vkHeightDoubleLog_ge t
  exact one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow hL (by norm_num)) (Real.one_le_rpow hLL (by norm_num))

theorem t1_vkHeightWidth_pos {c : ℝ} (hc : 0 < c) (t : ℝ) : 0 < t1_vkHeightWidth c t :=
  div_pos hc (zero_lt_one.trans_le (t1_vkHeightDenom_ge_one t))

theorem t1_vkHeightWidth_le {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : t1_vkHeightWidth c t ≤ c := by
  unfold t1_vkHeightWidth
  exact div_le_self hc (t1_vkHeightDenom_ge_one t)

theorem t1_vkHeightWidth_antitone_abs {c t u : ℝ} (hc : 0 ≤ c) (htu : |t| ≤ |u|) :
    t1_vkHeightWidth c u ≤ t1_vkHeightWidth c t := by
  have hp : 0 < |t|+t1_vkHeightBase := by unfold t1_vkHeightBase; positivity
  have hLt : 0 < t1_vkHeightLog t := (Real.exp_pos _).trans_le (t1_vkHeightLog_ge t)
  have hL : t1_vkHeightLog t ≤ t1_vkHeightLog u :=
    Real.log_le_log hp (add_le_add_left htu _)
  have hLL := Real.log_le_log hLt hL
  have hD : t1_vkHeightDenom t ≤ t1_vkHeightDenom u :=
    mul_le_mul (Real.rpow_le_rpow hLt.le hL (by norm_num))
      (Real.rpow_le_rpow (zero_le_one.trans (t1_vkHeightDoubleLog_ge t)) hLL (by norm_num))
      (by positivity [t1_vkHeightDoubleLog_ge t]) (by positivity [hLt.trans_le hL])
  exact div_le_div_of_nonneg_left hc (zero_lt_one.trans_le (t1_vkHeightDenom_ge_one t)) hD

theorem t1_vkHeightDenom_le_log (t : ℝ) : t1_vkHeightDenom t ≤ t1_vkHeightLog t := by
  have hL := (Real.exp_pos _).trans_le (t1_vkHeightLog_ge t)
  have hLL : 0 ≤ Real.log (t1_vkHeightLog t) := zero_le_one.trans (t1_vkHeightDoubleLog_ge t)
  have hle : Real.log (t1_vkHeightLog t) ≤ t1_vkHeightLog t := by
    linarith [Real.log_le_sub_one_of_pos hL]
  unfold t1_vkHeightDenom
  calc
    _ ≤ (t1_vkHeightLog t)^((2 : ℝ)/3)*(t1_vkHeightLog t)^((1 : ℝ)/3) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hLL hle (by norm_num))
        (Real.rpow_nonneg hL.le _)
    _ = _ := by rw [← Real.rpow_add hL,show (2 : ℝ)/3+1/3=1 by norm_num,Real.rpow_one]

theorem t1_vkHeightDenom_le_linear (t : ℝ) : t1_vkHeightDenom t ≤ |t|+t1_vkHeightBase := by
  have h0 : 0 < |t|+t1_vkHeightBase := by unfold t1_vkHeightBase; positivity
  exact (t1_vkHeightDenom_le_log t).trans (by
    unfold t1_vkHeightLog
    linarith [Real.log_le_sub_one_of_pos h0])

theorem t1_vkHeightWidth_abs (c t : ℝ) :
    t1_vkHeightWidth c |t| = t1_vkHeightWidth c t := by
  simp only [t1_vkHeightWidth,t1_vkHeightDenom,t1_vkHeightLog,abs_abs]

end Markov
