import T1VKHeightSchedule

/-! Exact powers on the two contour edges and at the chosen height. -/
noncomputable section
open Filter
namespace Markov

def t1_vkContourRight (x : ℝ) : ℝ := 1+1/Real.log x

theorem t1_vkContourRight_bounds (x : ℝ) (hx : 1 ≤ Real.log x) :
    1 ≤ t1_vkContourRight x ∧ t1_vkContourRight x ≤ 2 := by
  have hL := zero_lt_one.trans_le hx
  have hdiv := (div_le_one hL).2 hx
  unfold t1_vkContourRight
  constructor <;> linarith [div_pos zero_lt_one hL]

theorem t1_vkContourRight_power (x : ℝ) (hx : 0 < x) (hl : 0 < Real.log x) :
    x^(t1_vkContourRight x) = Real.exp 1*x := by
  rw [Real.rpow_def_of_pos hx,t1_vkContourRight,
    show Real.log x*(1+1/Real.log x) = 1+Real.log x by field_simp [hl.ne']; ring,
    Real.exp_add,Real.exp_log hx]

theorem t1_vkContourHeight_negThree (x : ℝ) :
    (t1_vkContourHeight x)^(-(3 : ℝ)) = Real.exp (-3*t1_vkWeight x) := by
  rw [t1_vkContourHeight,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  congr 1
  ring

theorem t1_vkContourLeft_power (c x T : ℝ) (hx : 0 < x) (hl : 0 < Real.log x)
    (hd : c*t1_vkWeight x/(2*Real.log x) ≤ t1_vkDiskWidth c T) :
    x^(t1_vkContourLeft c T) ≤ x*Real.exp (-(c/16)*t1_vkWeight x) := by
  have hb := (div_le_iff₀ (show 0 < 2*Real.log x by positivity)).1 hd
  rw [Real.rpow_def_of_pos hx,t1_vkContourLeft,
    show Real.log x*(1-t1_vkDiskWidth c T/8) =
      Real.log x+(-(Real.log x*t1_vkDiskWidth c T/8)) by ring,
    Real.exp_add,Real.exp_log hx]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hx.le

theorem t1_vkContour_eventual_scales {c : ℝ} (hc : 0 < c) (hc' : c ≤ 1/4) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ t1_vkContourHeight x ∧
      1 ≤ t1_vkContourRight x ∧ t1_vkContourRight x ≤ 2 ∧
      x^(t1_vkContourLeft c (t1_vkContourHeight x)) ≤
        x*Real.exp (-(c/16)*t1_vkWeight x) ∧
      x^(t1_vkContourRight x)*(t1_vkContourHeight x)^(-(3 : ℝ)) ≤
        Real.exp 1*(x*Real.exp (-(c/16)*t1_vkWeight x)) := by
  filter_upwards [t1_vkContourHeight_eventually_admissible hc] with x hx
  have hx1 : 1 ≤ x := by
    have h := Real.exp_le_exp.mpr (show (0 : ℝ)≤1 by norm_num)
    rw [Real.exp_zero] at h
    exact h.trans hx.1.le
  have hL := zero_lt_one.trans_le hx.2.2.1
  have hx0 := zero_lt_one.trans_le hx1
  have hW := t1_vkWeight_pos x hx.1
  obtain ⟨hr1,hr2⟩ := t1_vkContourRight_bounds x hx.2.2.1
  refine ⟨hx1,hx.2.1,hr1,hr2,t1_vkContourLeft_power c x _ hx0 hL hx.2.2.2,?_⟩
  rw [t1_vkContourRight_power x hx0 hL,t1_vkContourHeight_negThree]
  calc
    _ ≤ (Real.exp 1*x)*Real.exp (-(c/16)*t1_vkWeight x) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
    _ = _ := by ring

end Markov
