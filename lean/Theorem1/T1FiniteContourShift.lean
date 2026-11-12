import T1VerticalContourShift

/-! Quantitative finite contour displacement on the actual rectangle. -/
noncomputable section
open Complex Set Filter MeasureTheory
open scoped Interval
namespace Markov

def t1_verticalTrunc (F : ℂ → ℂ) (σ T : ℝ) : ℂ :=
  ∫ t : ℝ in -T..T, F (t1_verticalPoint σ t)

theorem t1_verticalTrunc_rect_bound {F : ℂ → ℂ} {a b T H : ℝ} (hab : a ≤ b)
    (hT : 0 ≤ T)
    (hF : DifferentiableOn ℂ F {s : ℂ | s.re ∈ Icc a b ∧ |s.im| ≤ T})
    (hB : ∀ x ∈ Icc a b, ‖F (t1_verticalPoint x T)‖ ≤ H ∧
      ‖F (t1_verticalPoint x (-T))‖ ≤ H) :
    ‖t1_verticalTrunc F b T‖ ≤ ‖t1_verticalTrunc F a T‖+2*(b-a)*H := by
  let P := ∫ x : ℝ in a..b, F (t1_verticalPoint x T)
  let N := ∫ x : ℝ in a..b, F (t1_verticalPoint x (-T))
  have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    (t1_verticalPoint a (-T)) (t1_verticalPoint b T) ?_
  swap
  · apply hF.mono
    intro s hs
    have hs' := hs
    change s.re ∈ [[(t1_verticalPoint a (-T)).re,(t1_verticalPoint b T).re]] ∧
      s.im ∈ [[(t1_verticalPoint a (-T)).im,(t1_verticalPoint b T).im]] at hs'
    rw [t1_verticalPoint_re,t1_verticalPoint_re,t1_verticalPoint_im,t1_verticalPoint_im,
      uIcc_of_le hab,uIcc_of_le (by linarith : -T ≤ T)] at hs'
    exact ⟨hs'.1,abs_le.mpr hs'.2⟩
  simp only [t1_verticalPoint_re,t1_verticalPoint_im] at hr
  change N-P+I • t1_verticalTrunc F b T-I • t1_verticalTrunc F a T = 0 at hr
  have he : I*t1_verticalTrunc F b T = I*t1_verticalTrunc F a T+(P-N) := by
    change N-P+I*t1_verticalTrunc F b T-I*t1_verticalTrunc F a T = 0 at hr
    linear_combination hr
  have hP : ‖P‖ ≤ H*(b-a) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x => F (t1_verticalPoint x T)) (a := a) (b := b) (C := H) ?_
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using h
    · intro x hx
      rw [uIoc_of_le hab] at hx
      exact (hB x ⟨hx.1.le,hx.2⟩).1
  have hN : ‖N‖ ≤ H*(b-a) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x => F (t1_verticalPoint x (-T))) (a := a) (b := b) (C := H) ?_
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using h
    · intro x hx
      rw [uIoc_of_le hab] at hx
      exact (hB x ⟨hx.1.le,hx.2⟩).2
  calc
    _ = ‖I*t1_verticalTrunc F b T‖ := by rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ ‖I*t1_verticalTrunc F a T‖+‖P-N‖ := by rw [he]; exact norm_add_le _ _
    _ ≤ ‖t1_verticalTrunc F a T‖+2*(b-a)*H := by
      rw [norm_mul,Complex.norm_I,one_mul]
      linarith [norm_sub_le P N]

theorem t1_verticalTrunc_integrable_majorant {F : ℂ → ℂ} {a T : ℝ} {g : ℝ → ℝ}
    (hT : 0 ≤ T) (hg : Integrable g) (hG : ∀ t, 0 ≤ g t)
    (hB : ∀ t ∈ Icc (-T) T, ‖F (t1_verticalPoint a t)‖ ≤ g t) :
    ‖t1_verticalTrunc F a T‖ ≤ ∫ t : ℝ, g t := by
  rw [t1_verticalTrunc,intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  calc
    _ ≤ ∫ t : ℝ in Ioc (-T) T, g t := by
      apply norm_integral_le_of_norm_le hg.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hB t ⟨ht.1.le,ht.2⟩
    _ ≤ _ := setIntegral_le_integral hg (Eventually.of_forall hG)

end Markov
