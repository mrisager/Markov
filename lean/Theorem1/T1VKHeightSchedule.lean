import T1VKDiskGeometry

/-! The height exp(ω(x)) and the exact logarithmic exponents in the
Vinogradov–Korobov rectangle. -/
noncomputable section
open Filter Asymptotics
namespace Markov

def t1_vkContourHeight (x : ℝ) : ℝ := Real.exp (t1_vkWeight x)

theorem t1_vkWeight_height_exponents (x : ℝ) (hx : Real.exp 1 < x) :
    (t1_vkWeight x)^((2 : ℝ)/3)*(Real.log (Real.log x))^((1 : ℝ)/3) =
      Real.log x/t1_vkWeight x := by
  have hw := t1_vkWeight_pos x hx
  have hl : 1 < Real.log x := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_lt_log (Real.exp_pos _) hx
  have hl0 : 0 < Real.log x := by linarith
  have hll := Real.log_pos hl
  apply (eq_div_iff hw.ne').2
  calc
    _ = (t1_vkWeight x)^((5 : ℝ)/3)*(Real.log (Real.log x))^((1 : ℝ)/3) := by
      rw [show (5 : ℝ)/3 = 2/3+1 by norm_num,Real.rpow_add hw,Real.rpow_one]
      ring
    _ = Real.log x := by
      rw [t1_vkWeight,Real.div_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hl0.le,← Real.rpow_mul hll.le,
        show ((3 : ℝ)/5)*(5/3) = 1 by norm_num,
        show ((1 : ℝ)/5)*(5/3) = 1/3 by norm_num,Real.rpow_one]
      exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos hll _).ne'

theorem t1_vkContourHeight_eventually_admissible {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.exp 1 < x ∧ 1 ≤ t1_vkContourHeight x ∧
      1 ≤ Real.log x ∧
      c*t1_vkWeight x/(2*Real.log x) ≤ t1_vkDiskWidth c (t1_vkContourHeight x) := by
  have hsmall := t1_vkWeight_isLittleO_log.bound (c := 1) (by norm_num)
  filter_upwards [eventually_gt_atTop (Real.exp 1),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    t1_vkWeight_tendsto.eventually_ge_atTop (max 1 (Real.log (1+t1_vkHeightBase))),hsmall]
    with x hx hll hW hsmallx
  change 1 ≤ Real.log (Real.log x) at hll
  let ω := t1_vkWeight x
  let T := t1_vkContourHeight x
  have hw := t1_vkWeight_pos x hx
  have hW1 : 1 ≤ ω := (le_max_left _ _).trans hW
  have hl : 1 < Real.log x := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_lt_log (Real.exp_pos _) hx
  have hl0 : 0 < Real.log x := by linarith
  have hwL : ω ≤ Real.log x := by
    simpa only [Real.norm_eq_abs,abs_of_pos hw,abs_of_pos hl0,one_mul] using hsmallx
  have hT0 : 0 < T := Real.exp_pos _
  have hT1 : 1 ≤ T := by
    change 1 ≤ Real.exp ω
    exact (Real.exp_zero.symm.trans_le (Real.exp_le_exp.mpr (by linarith)))
  have hBase : 0 < 1+t1_vkHeightBase := by unfold t1_vkHeightBase; positivity
  have hTall : 1+t1_vkHeightBase ≤ T := by
    rw [← Real.exp_log hBase]
    exact Real.exp_le_exp.mpr ((le_max_right _ _).trans hW)
  have hArg : 0 < |T+1|+t1_vkHeightBase := by unfold t1_vkHeightBase; positivity
  have hArg' : |T+1|+t1_vkHeightBase ≤ 2*T := by
    rw [abs_of_pos (by linarith : 0 < T+1)]
    linarith
  have hLog2 : Real.log 2 ≤ 1 := calc
    _ ≤ (2 : ℝ)-1 := Real.log_le_sub_one_of_pos (by norm_num)
    _ = _ := by norm_num
  have hL : t1_vkHeightLog (T+1) ≤ 2*ω := by
    calc
      _ ≤ Real.log (2*T) := Real.log_le_log hArg hArg'
      _ = Real.log 2+ω := by
        rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hT0.ne']
        change Real.log 2+Real.log (Real.exp ω) = _
        rw [Real.log_exp]
      _ ≤ _ := by linarith
  have hL0 : 0 < t1_vkHeightLog (T+1) := (Real.exp_pos _).trans_le (t1_vkHeightLog_ge _)
  have hLL : Real.log (t1_vkHeightLog (T+1)) ≤ 2*Real.log (Real.log x) := by
    have h := Real.log_le_log hL0 (hL.trans (mul_le_mul_of_nonneg_left hwL (by norm_num)))
    rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hl0.ne'] at h
    linarith
  have hD : t1_vkHeightDenom (T+1) ≤ 2*(Real.log x/ω) := calc
    _ ≤ (2*ω)^((2 : ℝ)/3)*(2*Real.log (Real.log x))^((1 : ℝ)/3) := by
      unfold t1_vkHeightDenom
      have hL' := Real.rpow_le_rpow hL0.le hL (by norm_num : (0 : ℝ)≤2/3)
      have hll0 := zero_le_one.trans (t1_vkHeightDoubleLog_ge (T+1))
      have hLL' := Real.rpow_le_rpow hll0 hLL (by norm_num : (0 : ℝ)≤1/3)
      exact mul_le_mul hL' hLL' (Real.rpow_nonneg hll0 _) (by positivity)
    _ = 2*(ω^((2 : ℝ)/3)*(Real.log (Real.log x))^((1 : ℝ)/3)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤2) hw.le,
        Real.mul_rpow (by norm_num : (0 : ℝ)≤2) (zero_le_one.trans hll)]
      have he : (2 : ℝ)^((2 : ℝ)/3)*(2 : ℝ)^((1 : ℝ)/3) = 2 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ)<2),show (2 : ℝ)/3+1/3=1 by norm_num,Real.rpow_one]
      calc
        _ = ((2 : ℝ)^((2 : ℝ)/3)*(2 : ℝ)^((1 : ℝ)/3))*
            (ω^((2 : ℝ)/3)*(Real.log (Real.log x))^((1 : ℝ)/3)) := by ring
        _ = _ := by rw [he]
    _ = _ := by rw [t1_vkWeight_height_exponents x hx]
  refine ⟨hx,hT1,hl.le,?_⟩
  change c*ω/(2*Real.log x) ≤ t1_vkDiskWidth c T
  rw [t1_vkDiskWidth,abs_of_pos hT0,t1_vkHeightWidth]
  calc
    _ = c/(2*(Real.log x/ω)) := by field_simp [hw.ne',hl0.ne']
    _ ≤ _ := div_le_div_of_nonneg_left hc.le (zero_lt_one.trans_le (t1_vkHeightDenom_ge_one _)) hD

end Markov
