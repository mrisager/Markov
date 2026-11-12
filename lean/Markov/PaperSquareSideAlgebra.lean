import Markov.SquareChartAlgebra

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- The boundary parameter map forced by the literal paper generators. -/
def paperSquareSideParameter (t : ℝ) : ℝ := (5*t+3)/(3*t+5)

/-- First coordinate of the explicit square chart, before taking a subtype. -/
def paperSquareRawFirst (z : UpperHalfPlane) : ℝ :=
  (z.re ^ 2 + z.im ^ 2 - 1 - 2*z.re) / (z.re ^ 2 + z.im ^ 2 + 1)

/-- Second coordinate of the explicit square chart, before taking a subtype. -/
def paperSquareRawSecond (z : UpperHalfPlane) : ℝ :=
  (z.re ^ 2 + z.im ^ 2 - 1 + 2*z.re) / (z.re ^ 2 + z.im ^ 2 + 1)

/-- Specialized real coordinate of the literal A action on its source side. -/
theorem paperSquare_A_re (z : UpperHalfPlane) (hz : z.re = 1) :
    (paperGeneratorASL • z).re = -(z.im ^ 2) / (1 + z.im ^ 2) := by
  have hr := congrArg Complex.re (paperGeneratorA_moebius z)
  norm_num [Complex.div_re, Complex.normSq_apply, hz] at hr
  change (paperGeneratorASL • z).re = _ at hr
  convert hr using 1
  ring

/-- Specialized height of the literal A action on its source side. -/
theorem paperSquare_A_im (z : UpperHalfPlane) (hz : z.re = 1) :
    (paperGeneratorASL • z).im = z.im / (1 + z.im ^ 2) := by
  have hi := congrArg Complex.im (paperGeneratorA_moebius z)
  norm_num [Complex.div_im, Complex.normSq_apply, hz] at hi
  change (paperGeneratorASL • z).im = _ at hi
  convert hi using 1
  ring

/-- Specialized real coordinate of the literal B action on its source side. -/
theorem paperSquare_B_re (z : UpperHalfPlane) (hz : z.re = -1) :
    (paperGeneratorBSL • z).re = z.im ^ 2 / (1 + z.im ^ 2) := by
  have hr := congrArg Complex.re (paperGeneratorB_moebius z)
  norm_num [Complex.div_re, Complex.normSq_apply, hz] at hr
  change (paperGeneratorBSL • z).re = _ at hr
  convert hr using 1
  ring

/-- Specialized height of the literal B action on its source side. -/
theorem paperSquare_B_im (z : UpperHalfPlane) (hz : z.re = -1) :
    (paperGeneratorBSL • z).im = z.im / (1 + z.im ^ 2) := by
  have hi := congrArg Complex.im (paperGeneratorB_moebius z)
  norm_num [Complex.div_im, Complex.normSq_apply, hz] at hi
  change (paperGeneratorBSL • z).im = _ at hi
  convert hi using 1
  ring

/-- The shared boundary-coordinate computation in the height parameter. -/
theorem paperSquareSideParameter_height (y : ℝ) :
    paperSquareSideParameter ((y^2-2)/(y^2+2)) = (2*y^2-1)/(2*y^2+1) := by
  have h2 : y^2+2 ≠ 0 := by positivity
  have h3 : 2*y^2+1 ≠ 0 := by positivity
  have heq : 3*((y^2-2)/(y^2+2))+5 = 4*(2*y^2+1)/(y^2+2) := by
    field_simp
    ring
  unfold paperSquareSideParameter
  rw [heq]
  field_simp
  ring

/-- The top edge is the original right vertical side. -/
theorem paperSquare_rightVertical_coordinates (z : UpperHalfPlane) (hz : z.re = 1) :
    paperSquareRawFirst z = (z.im^2-2)/(z.im^2+2) ∧ paperSquareRawSecond z = 1 := by
  unfold paperSquareRawFirst paperSquareRawSecond
  rw [hz]
  have h : z.im^2+2 ≠ 0 := by positivity
  constructor <;> field_simp <;> ring

/-- The right edge is the original left vertical side. -/
theorem paperSquare_leftVertical_coordinates (z : UpperHalfPlane) (hz : z.re = -1) :
    paperSquareRawFirst z = 1 ∧ paperSquareRawSecond z = (z.im^2-2)/(z.im^2+2) := by
  unfold paperSquareRawFirst paperSquareRawSecond
  rw [hz]
  have h : z.im^2+2 ≠ 0 := by positivity
  constructor <;> field_simp <;> ring

/-- A induces precisely the non-affine parameter map from top to bottom. -/
theorem paperSquare_A_coordinates (z : UpperHalfPlane) (hz : z.re = 1) :
    paperSquareRawFirst (paperGeneratorASL • z) =
      paperSquareSideParameter (paperSquareRawFirst z) ∧
    paperSquareRawSecond (paperGeneratorASL • z) = -1 := by
  rw [(paperSquare_rightVertical_coordinates z hz).1, paperSquareSideParameter_height]
  unfold paperSquareRawFirst paperSquareRawSecond
  rw [paperSquare_A_re z hz, paperSquare_A_im z hz]
  have h : 1+z.im^2 ≠ 0 := by positivity
  have h2 : 2*z.im^2+1 ≠ 0 := by positivity
  have hN : (-(z.im^2)/(1+z.im^2))^2 + (z.im/(1+z.im^2))^2 =
      z.im^2/(1+z.im^2) := by
    field_simp
    ring
  rw [hN]
  have hden : z.im^2/(1+z.im^2)+1 = (2*z.im^2+1)/(1+z.im^2) := by
    field_simp
    ring
  rw [hden]
  constructor <;> field_simp <;> ring

/-- B induces precisely the same parameter map from right to left. -/
theorem paperSquare_B_coordinates (z : UpperHalfPlane) (hz : z.re = -1) :
    paperSquareRawFirst (paperGeneratorBSL • z) = -1 ∧
    paperSquareRawSecond (paperGeneratorBSL • z) =
      paperSquareSideParameter (paperSquareRawSecond z) := by
  rw [(paperSquare_leftVertical_coordinates z hz).2, paperSquareSideParameter_height]
  unfold paperSquareRawFirst paperSquareRawSecond
  rw [paperSquare_B_re z hz, paperSquare_B_im z hz]
  have h : 1+z.im^2 ≠ 0 := by positivity
  have h2 : 2*z.im^2+1 ≠ 0 := by positivity
  have hN : (z.im^2/(1+z.im^2))^2 + (z.im/(1+z.im^2))^2 =
      z.im^2/(1+z.im^2) := by
    field_simp
    ring
  rw [hN]
  have hden : z.im^2/(1+z.im^2)+1 = (2*z.im^2+1)/(1+z.im^2) := by
    field_simp
    ring
  rw [hden]
  constructor <;> field_simp <;> ring

/-- Inverse of the literal side parameter map. -/
def paperSquareSideParameterInverse (t : ℝ) : ℝ := (5*t-3)/(5-3*t)

theorem paperSquareSideParameter_den_pos {t : ℝ} (ht : -1 ≤ t) : 0 < 3*t+5 := by
  linarith

theorem paperSquareSideParameterInverse_den_pos {t : ℝ} (ht : t ≤ 1) : 0 < 5-3*t := by
  linarith

theorem paperSquareSideParameter_mem_Icc {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    paperSquareSideParameter t ∈ Set.Icc (-1 : ℝ) 1 := by
  have hd := paperSquareSideParameter_den_pos ht.1
  constructor
  · unfold paperSquareSideParameter
    rw [le_div_iff₀ hd]
    linarith [ht.1]
  · unfold paperSquareSideParameter
    rw [div_le_iff₀ hd]
    linarith [ht.2]

theorem paperSquareSideParameterInverse_mem_Icc {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    paperSquareSideParameterInverse t ∈ Set.Icc (-1 : ℝ) 1 := by
  have hd := paperSquareSideParameterInverse_den_pos ht.2
  constructor
  · unfold paperSquareSideParameterInverse
    rw [le_div_iff₀ hd]
    linarith [ht.1]
  · unfold paperSquareSideParameterInverse
    rw [div_le_iff₀ hd]
    linarith [ht.2]

theorem paperSquareSideParameter_mem_Ioo {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    paperSquareSideParameter t ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hd := paperSquareSideParameter_den_pos ht.1.le
  constructor
  · unfold paperSquareSideParameter
    rw [lt_div_iff₀ hd]
    linarith [ht.1]
  · unfold paperSquareSideParameter
    rw [div_lt_iff₀ hd]
    linarith [ht.2]

theorem paperSquareSideParameterInverse_mem_Ioo {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    paperSquareSideParameterInverse t ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hd := paperSquareSideParameterInverse_den_pos ht.2.le
  constructor
  · unfold paperSquareSideParameterInverse
    rw [lt_div_iff₀ hd]
    linarith [ht.1]
  · unfold paperSquareSideParameterInverse
    rw [div_lt_iff₀ hd]
    linarith [ht.2]

theorem paperSquareSideParameter_left_inv {t : ℝ} (ht : -1 ≤ t) :
    paperSquareSideParameterInverse (paperSquareSideParameter t) = t := by
  have hd := ne_of_gt (paperSquareSideParameter_den_pos ht)
  have hf : paperSquareSideParameter t * (3*t+5) = 5*t+3 := by
    exact div_mul_cancel₀ _ hd
  have hD : 5-3*paperSquareSideParameter t ≠ 0 := by
    intro h
    have hu : paperSquareSideParameter t = 5/3 := by linarith
    rw [hu] at hf
    nlinarith
  unfold paperSquareSideParameterInverse
  apply (div_eq_iff hD).mpr
  nlinarith [hf]

theorem paperSquareSideParameter_right_inv {t : ℝ} (ht : t ≤ 1) :
    paperSquareSideParameter (paperSquareSideParameterInverse t) = t := by
  have hd := ne_of_gt (paperSquareSideParameterInverse_den_pos ht)
  have hf : paperSquareSideParameterInverse t * (5-3*t) = 5*t-3 := by
    exact div_mul_cancel₀ _ hd
  have hD : 3*paperSquareSideParameterInverse t+5 ≠ 0 := by
    intro h
    have hu : paperSquareSideParameterInverse t = -5/3 := by linarith
    rw [hu] at hf
    nlinarith
  unfold paperSquareSideParameter
  apply (div_eq_iff hD).mpr
  nlinarith [hf]

theorem paperSquareSideParameter_strictMonoOn :
    StrictMonoOn paperSquareSideParameter (Set.Icc (-1 : ℝ) 1) := by
  intro a ha b hb hab
  have hda := paperSquareSideParameter_den_pos ha.1
  have hdb := paperSquareSideParameter_den_pos hb.1
  unfold paperSquareSideParameter
  rw [div_lt_div_iff₀ hda hdb]
  nlinarith

theorem paperSquareSideParameter_neg_one : paperSquareSideParameter (-1) = -1 := by
  norm_num [paperSquareSideParameter]

theorem paperSquareSideParameter_one : paperSquareSideParameter 1 = 1 := by
  norm_num [paperSquareSideParameter]

/-- The forced edge map extends to an endpoint-preserving interval homeomorphism. -/
def paperSquareSideParameterHomeomorph :
    Set.Icc (-1 : ℝ) 1 ≃ₜ Set.Icc (-1 : ℝ) 1 where
  toFun t := ⟨paperSquareSideParameter t.val, paperSquareSideParameter_mem_Icc t.property⟩
  invFun t := ⟨paperSquareSideParameterInverse t.val,
    paperSquareSideParameterInverse_mem_Icc t.property⟩
  left_inv t := Subtype.ext (paperSquareSideParameter_left_inv t.property.1)
  right_inv t := Subtype.ext (paperSquareSideParameter_right_inv t.property.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold paperSquareSideParameter
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t
      exact ne_of_gt (paperSquareSideParameter_den_pos t.property.1)
  continuous_invFun := by
    apply Continuous.subtype_mk
    unfold paperSquareSideParameterInverse
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t
      exact ne_of_gt (paperSquareSideParameterInverse_den_pos t.property.2)

/-- The literal edge map is also a homeomorphism of the open edge. -/
def paperSquareOpenSideParameterHomeomorph :
    Set.Ioo (-1 : ℝ) 1 ≃ₜ Set.Ioo (-1 : ℝ) 1 where
  toFun t := ⟨paperSquareSideParameter t.val, paperSquareSideParameter_mem_Ioo t.property⟩
  invFun t := ⟨paperSquareSideParameterInverse t.val,
    paperSquareSideParameterInverse_mem_Ioo t.property⟩
  left_inv t := Subtype.ext (paperSquareSideParameter_left_inv t.property.1.le)
  right_inv t := Subtype.ext (paperSquareSideParameter_right_inv t.property.2.le)
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold paperSquareSideParameter
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t
      exact ne_of_gt (paperSquareSideParameter_den_pos t.property.1.le)
  continuous_invFun := by
    apply Continuous.subtype_mk
    unfold paperSquareSideParameterInverse
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t
      exact ne_of_gt (paperSquareSideParameterInverse_den_pos t.property.2.le)

end Markov
