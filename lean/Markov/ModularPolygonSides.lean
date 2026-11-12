import Markov.PaperCuspHolonomy

/-! Actual local side-pairing words and their quotient identifications.
The original paper quadrilateral and all four genuine sides are explicit;
its A/B side maps are actual homeomorphisms. No polygon coverage or global
boundary-equivalence theorem is assumed. -/
noncomputable section
open scoped MatrixGroups
open Set
namespace Markov

/-- The literal special-linear word for a circular side pairing. -/
theorem modular_T_pow_three_mul_S :
    ModularGroup.T ^ 3 * ModularGroup.S = modularGeneratorASL * modularGeneratorBSL := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      ModularGroup.coe_T, ModularGroup.coe_S, modularGeneratorASL, modularGeneratorBSL,
      modularGeneratorA, modularGeneratorB, Matrix.mul_apply, Fin.sum_univ_two]

theorem modular_T_pow_three_mul_S_mem_modularTraceSubgroup :
    ModularGroup.T ^ 3 * ModularGroup.S ∈ modularTraceSubgroup := by
  rw [modular_T_pow_three_mul_S]
  exact modularTraceSubgroup.mul_mem modularGeneratorASL_mem_modularTraceSubgroup
    modularGeneratorBSL_mem_modularTraceSubgroup

/-- The genuine SL lift of the sixth translation has a minus sign. -/
theorem neg_T_pow_six_mem_modularTraceSubgroup :
    -(ModularGroup.T ^ 6) ∈ modularTraceSubgroup := by
  have h := (inferInstance : modularTraceSubgroup.Normal).conj_mem
    paperCuspHolonomy paperCuspHolonomy_mem_modularTraceSubgroup ModularGroup.S⁻¹
  simpa [paperCuspHolonomy_eq_neg_conjugate_T_pow_six, mul_assoc] using h

/-- The actual circular side word, bundled in the actual acting subgroup. -/
def modularCircleSideWord (r : ℤ) : modularTraceSubgroup :=
  ⟨ModularGroup.T ^ r * (ModularGroup.T ^ 3 * ModularGroup.S) * (ModularGroup.T ^ r)⁻¹,
    (inferInstance : modularTraceSubgroup.Normal).conj_mem _
      modular_T_pow_three_mul_S_mem_modularTraceSubgroup _⟩

@[simp] theorem modularCircleSideWord_coe (r : ℤ) :
    (modularCircleSideWord r : SL(2, ℤ)) =
      ModularGroup.T ^ r * (ModularGroup.T ^ 3 * ModularGroup.S) * ModularGroup.T ^ (-r) := by
  rw [zpow_neg]
  rfl

/-- The exact circular side action, valid in particular for r=0,1,2. -/
theorem modularCircleSideWord_smul (r : ℤ) (z : UpperHalfPlane) :
    modularCircleSideWord r • (ModularGroup.T ^ r • z) =
      ModularGroup.T ^ (r + 3) • (ModularGroup.S • z) := by
  change (ModularGroup.T ^ r * (ModularGroup.T ^ 3 * ModularGroup.S) *
    (ModularGroup.T ^ r)⁻¹) • (ModularGroup.T ^ r • z) = _
  simp only [mul_smul, inv_smul_smul, zpow_add, zpow_ofNat]

theorem modularCircleSideWord_quotient (r : ℤ) (z : UpperHalfPlane) :
    modularTraceQuotientMk (ModularGroup.T ^ r • z) =
      modularTraceQuotientMk (ModularGroup.T ^ (r + 3) • (ModularGroup.S • z)) := by
  have h := modularTraceQuotientMk_smul (modularCircleSideWord r) (ModularGroup.T ^ r • z)
  rw [modularCircleSideWord_smul] at h
  exact h.symm

/-- The actual vertical side word retains the necessary central sign. -/
def modularVerticalSideWord : modularTraceSubgroup :=
  ⟨-(ModularGroup.T ^ 6), neg_T_pow_six_mem_modularTraceSubgroup⟩

@[simp] theorem modularVerticalSideWord_coe :
    (modularVerticalSideWord : SL(2, ℤ)) = -(ModularGroup.T ^ 6) := rfl

theorem modularVerticalSideWord_smul (z : UpperHalfPlane) :
    modularVerticalSideWord • z = (6 : ℝ) +ᵥ z := by
  change -(ModularGroup.T ^ 6) • z = _
  rw [ModularGroup.SL_neg_smul]
  simpa only [zpow_ofNat, Int.cast_ofNat] using UpperHalfPlane.modular_T_zpow_smul z 6

theorem modularVerticalSideWord_quotient (z : UpperHalfPlane) :
    modularTraceQuotientMk z = modularTraceQuotientMk ((6 : ℝ) +ᵥ z) := by
  have h := modularTraceQuotientMk_smul modularVerticalSideWord z
  rw [modularVerticalSideWord_smul] at h
  exact h.symm

/-- The original paper's ideal quadrilateral, as an actual subset of H.
No orbit coverage assertion is part of this definition. -/
def paperIdealQuadrilateral : Set UpperHalfPlane :=
  {z | -1 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.re ^ 2 + z.re + z.im ^ 2 ∧
    0 ≤ z.re ^ 2 - z.re + z.im ^ 2}

def paperRightVerticalSide : Set UpperHalfPlane := {z | z.re = 1}
def paperLeftVerticalSide : Set UpperHalfPlane := {z | z.re = -1}
def paperLeftSemicircleSide : Set UpperHalfPlane := {z | z.re ^ 2 + z.re + z.im ^ 2 = 0}
def paperRightSemicircleSide : Set UpperHalfPlane := {z | z.re ^ 2 - z.re + z.im ^ 2 = 0}

theorem paperLeftSemicircleSide_re_bounds {z : UpperHalfPlane}
    (hz : z ∈ paperLeftSemicircleSide) : -1 < z.re ∧ z.re < 0 := by
  change z.re ^ 2 + z.re + z.im ^ 2 = 0 at hz
  have hy := sq_pos_of_pos z.im_pos
  constructor <;> nlinarith [sq_nonneg z.re, sq_nonneg (z.re + 1)]

theorem paperRightSemicircleSide_re_bounds {z : UpperHalfPlane}
    (hz : z ∈ paperRightSemicircleSide) : 0 < z.re ∧ z.re < 1 := by
  change z.re ^ 2 - z.re + z.im ^ 2 = 0 at hz
  have hy := sq_pos_of_pos z.im_pos
  constructor <;> nlinarith [sq_nonneg z.re, sq_nonneg (z.re - 1)]

theorem paperGeneratorA_moebius (z : UpperHalfPlane) :
    ((paperGeneratorASL • z : UpperHalfPlane) : ℂ) = ((z : ℂ) - 1) / (2 - (z : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [paperGeneratorASL, paperGeneratorA, sub_eq_add_neg, add_comm]

theorem paperGeneratorB_moebius (z : UpperHalfPlane) :
    ((paperGeneratorBSL • z : UpperHalfPlane) : ℂ) = ((z : ℂ) + 1) / ((z : ℂ) + 2) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [paperGeneratorBSL, paperGeneratorB]

/-- The exact signed circle expression for the actual A action. -/
theorem paperGeneratorA_circle_identity (z : UpperHalfPlane) :
    (paperGeneratorASL • z).re ^ 2 + (paperGeneratorASL • z).re +
        (paperGeneratorASL • z).im ^ 2 =
      (z.re - 1) / ((2 - z.re) ^ 2 + z.im ^ 2) := by
  have hD : (2 - z.re) ^ 2 + z.im ^ 2 ≠ 0 := by
    have hy := sq_pos_of_pos z.im_pos
    nlinarith [sq_nonneg (2 - z.re)]
  have hr := congrArg Complex.re (paperGeneratorA_moebius z)
  have hi := congrArg Complex.im (paperGeneratorA_moebius z)
  norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply] at hr hi
  change (paperGeneratorASL • z).re = _ at hr
  change (paperGeneratorASL • z).im = _ at hi
  rw [hr, hi]
  field_simp [hD, ← pow_two]
  ring

/-- The exact signed circle expression for the actual B action. -/
theorem paperGeneratorB_circle_identity (z : UpperHalfPlane) :
    (paperGeneratorBSL • z).re ^ 2 - (paperGeneratorBSL • z).re +
        (paperGeneratorBSL • z).im ^ 2 =
      -(z.re + 1) / ((z.re + 2) ^ 2 + z.im ^ 2) := by
  have hD : (z.re + 2) ^ 2 + z.im ^ 2 ≠ 0 := by
    have hy := sq_pos_of_pos z.im_pos
    nlinarith [sq_nonneg (z.re + 2)]
  have hr := congrArg Complex.re (paperGeneratorB_moebius z)
  have hi := congrArg Complex.im (paperGeneratorB_moebius z)
  norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply] at hr hi
  change (paperGeneratorBSL • z).re = _ at hr
  change (paperGeneratorBSL • z).im = _ at hi
  rw [hr, hi]
  field_simp [hD, ← pow_two]
  ring

/-- A maps precisely the right vertical line onto the left semicircle. -/
theorem paperGeneratorA_side_iff (z : UpperHalfPlane) :
    paperGeneratorASL • z ∈ paperLeftSemicircleSide ↔ z ∈ paperRightVerticalSide := by
  change _ = 0 ↔ z.re = 1
  rw [paperGeneratorA_circle_identity]
  have hD : (2 - z.re) ^ 2 + z.im ^ 2 ≠ 0 := by
    have hy := sq_pos_of_pos z.im_pos
    nlinarith [sq_nonneg (2 - z.re)]
  rw [div_eq_zero_iff, or_iff_left hD, sub_eq_zero]

/-- B maps precisely the left vertical line onto the right semicircle. -/
theorem paperGeneratorB_side_iff (z : UpperHalfPlane) :
    paperGeneratorBSL • z ∈ paperRightSemicircleSide ↔ z ∈ paperLeftVerticalSide := by
  change _ = 0 ↔ z.re = -1
  rw [paperGeneratorB_circle_identity]
  have hD : (z.re + 2) ^ 2 + z.im ^ 2 ≠ 0 := by
    have hy := sq_pos_of_pos z.im_pos
    nlinarith [sq_nonneg (z.re + 2)]
  rw [div_eq_zero_iff, or_iff_left hD, neg_eq_zero, add_eq_zero_iff_eq_neg]

theorem paperGeneratorA_inv_side_iff (z : UpperHalfPlane) :
    paperGeneratorASL⁻¹ • z ∈ paperRightVerticalSide ↔ z ∈ paperLeftSemicircleSide := by
  simpa only [smul_inv_smul] using (paperGeneratorA_side_iff (paperGeneratorASL⁻¹ • z)).symm

theorem paperGeneratorB_inv_side_iff (z : UpperHalfPlane) :
    paperGeneratorBSL⁻¹ • z ∈ paperLeftVerticalSide ↔ z ∈ paperRightSemicircleSide := by
  simpa only [smul_inv_smul] using (paperGeneratorB_side_iff (paperGeneratorBSL⁻¹ • z)).symm

/-- The actual A side pairing is a homeomorphism, with actual inverse A^-1. -/
def paperGeneratorA_sideHomeomorph : paperRightVerticalSide ≃ₜ paperLeftSemicircleSide where
  toFun z := ⟨paperGeneratorASL • z.val, (paperGeneratorA_side_iff z.val).mpr z.property⟩
  invFun z := ⟨paperGeneratorASL⁻¹ • z.val, (paperGeneratorA_inv_side_iff z.val).mpr z.property⟩
  left_inv _ := Subtype.ext (inv_smul_smul _ _)
  right_inv _ := Subtype.ext (smul_inv_smul _ _)
  continuous_toFun := ((modularInteger_isometry paperGeneratorASL).continuous.comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((modularInteger_isometry paperGeneratorASL⁻¹).continuous.comp
    continuous_subtype_val).subtype_mk _

/-- The actual B side pairing is a homeomorphism, with actual inverse B^-1. -/
def paperGeneratorB_sideHomeomorph : paperLeftVerticalSide ≃ₜ paperRightSemicircleSide where
  toFun z := ⟨paperGeneratorBSL • z.val, (paperGeneratorB_side_iff z.val).mpr z.property⟩
  invFun z := ⟨paperGeneratorBSL⁻¹ • z.val, (paperGeneratorB_inv_side_iff z.val).mpr z.property⟩
  left_inv _ := Subtype.ext (inv_smul_smul _ _)
  right_inv _ := Subtype.ext (smul_inv_smul _ _)
  continuous_toFun := ((modularInteger_isometry paperGeneratorBSL).continuous.comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((modularInteger_isometry paperGeneratorBSL⁻¹).continuous.comp
    continuous_subtype_val).subtype_mk _

theorem paperGeneratorA_quotient (z : UpperHalfPlane) :
    modularTraceQuotientMk (paperGeneratorASL • z) = modularTraceQuotientMk z := by
  apply modularTraceQuotientMk_ambient_smul
  rw [← paperTraceSubgroup_eq_modularTraceSubgroup]
  exact paperGeneratorASL_mem_paperTraceSubgroup

theorem paperGeneratorB_quotient (z : UpperHalfPlane) :
    modularTraceQuotientMk (paperGeneratorBSL • z) = modularTraceQuotientMk z := by
  apply modularTraceQuotientMk_ambient_smul
  rw [← paperTraceSubgroup_eq_modularTraceSubgroup]
  exact paperGeneratorBSL_mem_paperTraceSubgroup

/-- The reverse pairing uses the genuine inverse subgroup element. -/
theorem modularCircleSideWord_inv_smul (r : ℤ) (z : UpperHalfPlane) :
    (modularCircleSideWord r)⁻¹ • (ModularGroup.T ^ (r + 3) • (ModularGroup.S • z)) =
      ModularGroup.T ^ r • z := by
  rw [← modularCircleSideWord_smul r z, inv_smul_smul]

@[simp] theorem paperGeneratorA_sideHomeomorph_apply (z : paperRightVerticalSide) :
    (paperGeneratorA_sideHomeomorph z : UpperHalfPlane) = paperGeneratorASL • z.val := rfl

@[simp] theorem paperGeneratorA_sideHomeomorph_symm_apply (z : paperLeftSemicircleSide) :
    (paperGeneratorA_sideHomeomorph.symm z : UpperHalfPlane) = paperGeneratorASL⁻¹ • z.val := rfl

@[simp] theorem paperGeneratorB_sideHomeomorph_apply (z : paperLeftVerticalSide) :
    (paperGeneratorB_sideHomeomorph z : UpperHalfPlane) = paperGeneratorBSL • z.val := rfl

@[simp] theorem paperGeneratorB_sideHomeomorph_symm_apply (z : paperRightSemicircleSide) :
    (paperGeneratorB_sideHomeomorph.symm z : UpperHalfPlane) = paperGeneratorBSL⁻¹ • z.val := rfl

theorem paperGeneratorA_image_side :
    (paperGeneratorASL • ·) '' paperRightVerticalSide = paperLeftSemicircleSide := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (paperGeneratorA_side_iff w).mpr hw
  · intro hz
    exact ⟨paperGeneratorASL⁻¹ • z, (paperGeneratorA_inv_side_iff z).mpr hz,
      smul_inv_smul _ _⟩

theorem paperGeneratorB_image_side :
    (paperGeneratorBSL • ·) '' paperLeftVerticalSide = paperRightSemicircleSide := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (paperGeneratorB_side_iff w).mpr hw
  · intro hz
    exact ⟨paperGeneratorBSL⁻¹ • z, (paperGeneratorB_inv_side_iff z).mpr hz,
      smul_inv_smul _ _⟩

theorem paperRightVerticalSide_subset_quadrilateral :
    paperRightVerticalSide ⊆ paperIdealQuadrilateral := by
  intro z hz
  change z.re = 1 at hz
  change -1 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.re ^ 2 + z.re + z.im ^ 2 ∧
    0 ≤ z.re ^ 2 - z.re + z.im ^ 2
  rw [hz]
  refine ⟨by norm_num, le_rfl, ?_, ?_⟩ <;> positivity

theorem paperLeftVerticalSide_subset_quadrilateral :
    paperLeftVerticalSide ⊆ paperIdealQuadrilateral := by
  intro z hz
  change z.re = -1 at hz
  change -1 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.re ^ 2 + z.re + z.im ^ 2 ∧
    0 ≤ z.re ^ 2 - z.re + z.im ^ 2
  rw [hz]
  refine ⟨le_rfl, by norm_num, ?_, ?_⟩ <;> positivity

theorem paperLeftSemicircleSide_subset_quadrilateral :
    paperLeftSemicircleSide ⊆ paperIdealQuadrilateral := by
  intro z hz
  have hb := paperLeftSemicircleSide_re_bounds hz
  change z.re ^ 2 + z.re + z.im ^ 2 = 0 at hz
  change -1 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.re ^ 2 + z.re + z.im ^ 2 ∧
    0 ≤ z.re ^ 2 - z.re + z.im ^ 2
  exact ⟨hb.1.le, by linarith [hb.2], by linarith, by nlinarith [hb.2]⟩

theorem paperRightSemicircleSide_subset_quadrilateral :
    paperRightSemicircleSide ⊆ paperIdealQuadrilateral := by
  intro z hz
  have hb := paperRightSemicircleSide_re_bounds hz
  change z.re ^ 2 - z.re + z.im ^ 2 = 0 at hz
  change -1 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.re ^ 2 + z.re + z.im ^ 2 ∧
    0 ≤ z.re ^ 2 - z.re + z.im ^ 2
  exact ⟨by linarith [hb.1], hb.2.le, by nlinarith [hb.1], by linarith⟩

end Markov
