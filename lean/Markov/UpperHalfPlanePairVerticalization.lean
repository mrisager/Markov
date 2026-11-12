import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Tactic

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- An actual real determinant-one translation matrix. -/
def upperHalfPlaneTranslateSL (a : ℝ) : SL(2, ℝ) :=
  ⟨!![1, -a; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem upperHalfPlaneTranslateSL_re (a : ℝ) (z : UpperHalfPlane) :
    (upperHalfPlaneTranslateSL a • z).re = z.re-a := by
  change (((upperHalfPlaneTranslateSL a • z : UpperHalfPlane) : ℂ)).re = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  change (((1 : ℂ)*(z : ℂ)+((-a : ℝ) : ℂ))/((0 : ℂ)*(z : ℂ)+1)).re = _
  simp [sub_eq_add_neg]

/-- The actual circle-to-imaginary-axis matrix; scaling its second row by
1/(2r) gives determinant one without assuming a projective normalization. -/
def upperHalfPlaneCircleVerticalizer (a r : ℝ) (hr : 0 < r) : SL(2, ℝ) :=
  ⟨!![1, r-a; -(2*r)⁻¹, (a+r)/(2*r)], by
    rw [Matrix.det_fin_two]
    change 1*((a+r)/(2*r))-(r-a)*(-(2*r)⁻¹) = 1
    field_simp [hr.ne']
    ring⟩

/-- The literal circle equation makes the actual transformed real part zero. -/
theorem upperHalfPlaneCircleVerticalizer_re_zero
    (a r : ℝ) (hr : 0 < r) (z : UpperHalfPlane)
    (hcircle : (z.re-a)^2+z.im^2 = r^2) :
    (upperHalfPlaneCircleVerticalizer a r hr • z).re = 0 := by
  change (((upperHalfPlaneCircleVerticalizer a r hr • z : UpperHalfPlane) : ℂ)).re = 0
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  change (((1 : ℂ)*(z : ℂ)+((r-a : ℝ) : ℂ))/
    (((-(2*r)⁻¹ : ℝ) : ℂ)*(z : ℂ)+(((a+r)/(2*r) : ℝ) : ℂ))).re = 0
  rw [Complex.div_re, ← add_div]
  apply div_eq_zero_iff.mpr
  left
  have hn : (z.re+(r-a))*(-(2*r)⁻¹*z.re+(a+r)/(2*r))+
      z.im*(-(2*r)⁻¹*z.im) = 0 := by
    field_simp [hr.ne']
    nlinarith [hcircle]
  simpa only [one_mul, Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero] using hn

/-- Every actual pair of upper-half-plane points can be simultaneously moved
onto the imaginary axis by an actual SL(2,R) element. The witness is a
translation for a vertical pair and an explicit real-circle matrix otherwise. -/
theorem upperHalfPlane_pair_exists_verticalizer (z w : UpperHalfPlane) :
    ∃ g : SL(2, ℝ), (g • z).re = 0 ∧ (g • w).re = 0 := by
  by_cases hre : z.re = w.re
  · refine ⟨upperHalfPlaneTranslateSL z.re, ?_, ?_⟩
    · rw [upperHalfPlaneTranslateSL_re, sub_self]
    · rw [upperHalfPlaneTranslateSL_re, ← hre, sub_self]
  · have hd : 2*(w.re-z.re) ≠ 0 := by
      apply mul_ne_zero (by norm_num)
      exact sub_ne_zero.mpr (fun h => hre h.symm)
    let a : ℝ := (Complex.normSq (w : ℂ)-Complex.normSq (z : ℂ))/(2*(w.re-z.re))
    have ha : a*(2*(w.re-z.re)) = Complex.normSq (w : ℂ)-Complex.normSq (z : ℂ) :=
      div_mul_cancel₀ _ hd
    change a*(2*(w.re-z.re)) =
      (w.re*w.re+w.im*w.im)-(z.re*z.re+z.im*z.im) at ha
    have hspos : 0 < (z.re-a)^2+z.im^2 := by
      have hy := sq_pos_of_pos z.im_pos
      linarith [sq_nonneg (z.re-a)]
    let r : ℝ := Real.sqrt ((z.re-a)^2+z.im^2)
    have hr : 0 < r := Real.sqrt_pos.mpr hspos
    have hrsq : r^2 = (z.re-a)^2+z.im^2 := Real.sq_sqrt hspos.le
    have hw : (w.re-a)^2+w.im^2 = r^2 := by nlinarith [ha, hrsq]
    exact ⟨upperHalfPlaneCircleVerticalizer a r hr,
      upperHalfPlaneCircleVerticalizer_re_zero a r hr z hrsq.symm,
      upperHalfPlaneCircleVerticalizer_re_zero a r hr w hw⟩

/-- Distinct points remain distinct heights after simultaneous verticalization;
this follows from the actual group action, without a transitivity assumption. -/
theorem upperHalfPlane_distinct_pair_exists_verticalizer (z w : UpperHalfPlane) (hne : z ≠ w) :
    ∃ g : SL(2, ℝ), (g • z).re = 0 ∧ (g • w).re = 0 ∧ (g • z).im ≠ (g • w).im := by
  obtain ⟨g, hz, hw⟩ := upperHalfPlane_pair_exists_verticalizer z w
  refine ⟨g, hz, hw, ?_⟩
  intro him
  have he : g • z = g • w := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact hz.trans hw.symm
    · exact him
  apply hne
  have hi := congrArg (fun u : UpperHalfPlane => g⁻¹ • u) he
  simpa only [inv_smul_smul] using hi

/-- Actual determinant-one inversion reverses height order on the imaginary axis. -/
def upperHalfPlaneVerticalFlipSL : SL(2, ℝ) :=
  ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two]⟩

/-- The actual inversion keeps vertical points vertical and inverts their positive height. -/
theorem upperHalfPlaneVerticalFlipSL_on_imaginary (z : UpperHalfPlane) (hre : z.re = 0) :
    (upperHalfPlaneVerticalFlipSL • z).re = 0 ∧
      (upperHalfPlaneVerticalFlipSL • z).im = z.im⁻¹ := by
  have hc : ((upperHalfPlaneVerticalFlipSL • z : UpperHalfPlane) : ℂ) = -(z : ℂ)⁻¹ := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    change ((((0 : ℝ) : ℂ)*(z : ℂ)+((-1 : ℝ) : ℂ))/
      (((1 : ℝ) : ℂ)*(z : ℂ)+((0 : ℝ) : ℂ))) = _
    simp [neg_div]
  have hn : Complex.normSq (z : ℂ) = z.im*z.im := by
    change z.re*z.re+z.im*z.im = z.im*z.im
    rw [hre]
    simp
  constructor
  · change (((upperHalfPlaneVerticalFlipSL • z : UpperHalfPlane) : ℂ)).re = 0
    rw [hc, Complex.neg_re, Complex.inv_re]
    change -(z.re / Complex.normSq (z : ℂ)) = 0
    rw [hre, zero_div, neg_zero]
  · change (((upperHalfPlaneVerticalFlipSL • z : UpperHalfPlane) : ℂ)).im = z.im⁻¹
    rw [hc, Complex.neg_im, Complex.inv_im, hn]
    change -(-z.im/(z.im*z.im)) = z.im⁻¹
    field_simp [z.im_ne_zero]

/-- For an ordered pair of distinct actual points, an actual SL(2,R) witness
places both on the imaginary axis with the first height strictly smaller. -/
theorem upperHalfPlane_distinct_pair_exists_ordered_verticalizer
    (z w : UpperHalfPlane) (hne : z ≠ w) :
    ∃ g : SL(2, ℝ), (g • z).re = 0 ∧ (g • w).re = 0 ∧ (g • z).im < (g • w).im := by
  obtain ⟨g, hz, hw, him⟩ := upperHalfPlane_distinct_pair_exists_verticalizer z w hne
  rcases lt_or_gt_of_ne him with hlt | hgt
  · exact ⟨g, hz, hw, hlt⟩
  · refine ⟨upperHalfPlaneVerticalFlipSL*g, ?_, ?_, ?_⟩
    · rw [mul_smul]
      exact (upperHalfPlaneVerticalFlipSL_on_imaginary (g • z) hz).1
    · rw [mul_smul]
      exact (upperHalfPlaneVerticalFlipSL_on_imaginary (g • w) hw).1
    · simp only [mul_smul]
      rw [(upperHalfPlaneVerticalFlipSL_on_imaginary (g • z) hz).2,
        (upperHalfPlaneVerticalFlipSL_on_imaginary (g • w) hw).2]
      exact (inv_lt_inv₀ (g • z).im_pos (g • w).im_pos).mpr hgt

end Markov
