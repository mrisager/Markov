import T1MertensVKFromRegion

/-! Translate the conventional height log(|t|+2) to the harmless
larger shift used in the finite contour. The actual zero-free theorem
remains an explicit premise here. -/
noncomputable section
namespace Markov

def t1_vkRawHeightDenom (t : ℝ) : ℝ :=
  (Real.log (|t|+2))^((2 : ℝ)/3)*(Real.log (Real.log (|t|+2)))^((1 : ℝ)/3)

theorem t1_vkHeightBase_ge_two : 2 ≤ t1_vkHeightBase := by
  have h₁ : 1 ≤ Real.exp 1 := calc
    1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ _ := Real.exp_le_exp.mpr zero_le_one
  unfold t1_vkHeightBase
  linarith [Real.add_one_le_exp (Real.exp 1)]

theorem t1_vkHeightWidth_le_raw {c t : ℝ} (hc : 0 ≤ c)
    (ht : Real.exp 1 < |t|+2) :
    t1_vkHeightWidth c t ≤ c/t1_vkRawHeightDenom t := by
  have hL1 : 1 < Real.log (|t|+2) := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_lt_log (Real.exp_pos _) ht
  have hL0 : 0 < Real.log (|t|+2) := by linarith
  have hLL := Real.log_pos hL1
  have hL : Real.log (|t|+2) ≤ t1_vkHeightLog t :=
    Real.log_le_log (by positivity) (by linarith [t1_vkHeightBase_ge_two])
  have hLog := Real.log_le_log hL0 hL
  have hden : t1_vkRawHeightDenom t ≤ t1_vkHeightDenom t :=
    mul_le_mul (Real.rpow_le_rpow hL0.le hL (by norm_num))
      (Real.rpow_le_rpow hLL.le hLog (by norm_num))
      (Real.rpow_nonneg hLL.le _) (Real.rpow_nonneg (hL0.le.trans hL) _)
  have hden0 : 0 < t1_vkRawHeightDenom t :=
    mul_pos (Real.rpow_pos_of_pos hL0 _) (Real.rpow_pos_of_pos hLL _)
  exact div_le_div_of_nonneg_left hc hden0 hden

theorem t1_VKZeroFreeRegion_of_raw {c T : ℝ} (hc : 0 < c) (hT : 4 ≤ T)
    (hz : ∀ s : ℂ, T ≤ |s.im| → 1-c/t1_vkRawHeightDenom s.im ≤ s.re → riemannZeta s ≠ 0) :
    t1_VKZeroFreeRegion := by
  refine ⟨c,max T (Real.exp 1),hc,hT.trans (le_max_left _ _),?_⟩
  intro s hs hRe
  have hlarge : Real.exp 1 < |s.im|+2 := by linarith [(le_max_right T (Real.exp 1)).trans hs]
  have hw := t1_vkHeightWidth_le_raw hc.le hlarge
  exact hz s ((le_max_left _ _).trans hs) (by linarith)

end Markov
