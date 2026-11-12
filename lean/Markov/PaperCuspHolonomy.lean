import Markov.ModularTraceCyclicQuotient
import Markov.HyperbolicTranslationLength
import Markov.HyperbolicFixedPointTrace
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo

/-! The literal commutator of the original paper generators is a genuine
nontrivial parabolic modular matrix. Its action has no upper-half-plane fixed
point and has zero metric translation length. No cusp topology is asserted. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- The actual original-generator commutator, in the stated marking. -/
def paperCuspHolonomy : SL(2, ℤ) := ⁅paperGeneratorASL, paperGeneratorBSL⁆

theorem paperCuspHolonomy_mem_modularTraceSubgroup :
    paperCuspHolonomy ∈ modularTraceSubgroup := by
  rw [modularTraceSubgroup_eq_commutator]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem coe_paperCuspHolonomy :
    (paperCuspHolonomy : IntMatrixTwo) = !![-1, 0; 6, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperCuspHolonomy, commutatorElement_def,
      paperGeneratorASL, paperGeneratorA, paperGeneratorBSL, paperGeneratorB,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- The sign and exponent are identities already in `SL(2,ℤ)`. -/
theorem paperCuspHolonomy_eq_neg_conjugate_T_pow_six :
    paperCuspHolonomy = -(ModularGroup.S * ModularGroup.T ^ 6 * ModularGroup.S⁻¹) := by
  apply Subtype.ext
  rw [coe_paperCuspHolonomy]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, ModularGroup.coe_S, ModularGroup.coe_T,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem paperCuspHolonomy_trace : (paperCuspHolonomy : IntMatrixTwo).trace = -2 := by
  rw [coe_paperCuspHolonomy]
  norm_num [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]

theorem paperCuspHolonomy_ne_one : paperCuspHolonomy ≠ 1 := by
  intro h
  have hh := congrArg (fun g : SL(2, ℤ) => g 1 0) h
  change (paperCuspHolonomy : IntMatrixTwo) 1 0 = 0 at hh
  rw [coe_paperCuspHolonomy] at hh
  norm_num at hh

theorem paperCuspHolonomy_ne_neg_one : paperCuspHolonomy ≠ -1 := by
  intro h
  have hh := congrArg (fun g : SL(2, ℤ) => g 1 0) h
  change (paperCuspHolonomy : IntMatrixTwo) 1 0 = 0 at hh
  rw [coe_paperCuspHolonomy] at hh
  norm_num at hh

theorem paperCuspHolonomy_isParabolic :
    (paperCuspHolonomy : IntMatrixTwo).IsParabolic := by
  constructor
  · rintro ⟨r, hr⟩
    have hh := congrArg (fun M : IntMatrixTwo => M 1 0) hr
    rw [coe_paperCuspHolonomy] at hh
    change (0 : ℤ) = 6 at hh
    norm_num at hh
  · rw [coe_paperCuspHolonomy]
    norm_num [Matrix.discr_fin_two, Matrix.trace, Matrix.diag_apply,
      Matrix.det_fin_two, Fin.sum_univ_two]

/-- Projectivization removes the central minus sign, retaining the actual
sixth parabolic power and its conjugating matrix. -/
theorem paperCuspHolonomy_projective :
    modularIntegralProjectivization paperCuspHolonomy =
      modularIntegralProjectivization ModularGroup.S *
        modularIntegralProjectivization ModularGroup.T ^ 6 *
          (modularIntegralProjectivization ModularGroup.S)⁻¹ := by
  have hsign : modularIntegralProjectivization
      (-(ModularGroup.S * ModularGroup.T ^ 6 * ModularGroup.S⁻¹)) =
      modularIntegralProjectivization
        (ModularGroup.S * ModularGroup.T ^ 6 * ModularGroup.S⁻¹) :=
    (modularIntegralProjectivization_eq_iff _ _).mpr (Or.inr rfl)
  rw [paperCuspHolonomy_eq_neg_conjugate_T_pow_six, hsign]
  simp only [map_mul, map_pow, map_inv]

/-- The literal commutator acts by the conjugate of horizontal translation
by six on the genuine upper half-plane. -/
theorem paperCuspHolonomy_smul_S (z : UpperHalfPlane) :
    paperCuspHolonomy • (ModularGroup.S • z) =
      ModularGroup.S • (ModularGroup.T ^ 6 • z) := by
  rw [paperCuspHolonomy_eq_neg_conjugate_T_pow_six, ModularGroup.SL_neg_smul]
  simp only [mul_smul, inv_smul_smul]

theorem paperCuspHolonomy_no_fixed_point (z : UpperHalfPlane) :
    paperCuspHolonomy • z ≠ z := by
  intro hz
  let w := ModularGroup.S⁻¹ • z
  have hfix : paperCuspHolonomy • (ModularGroup.S • w) = ModularGroup.S • w := by
    simpa only [w, smul_inv_smul] using hz
  rw [paperCuspHolonomy_smul_S] at hfix
  have hT : ModularGroup.T ^ 6 • w = w := MulAction.injective _ hfix
  have hh := congrArg UpperHalfPlane.re hT
  have hact : ModularGroup.T ^ 6 • w = (6 : ℝ) +ᵥ w := by
    simpa only [zpow_ofNat, Int.cast_ofNat] using UpperHalfPlane.modular_T_zpow_smul w 6
  rw [hact, UpperHalfPlane.vadd_re] at hh
  linarith

/-- The displacement of the actual sixth translation decreases with the
height of the test point. -/
theorem modular_T_pow_six_displacement_bound (z : UpperHalfPlane) :
    dist z (ModularGroup.T ^ 6 • z) ≤ 6 / z.im := by
  have hact : ModularGroup.T ^ 6 • z = (6 : ℝ) +ᵥ z := by
    simpa only [zpow_ofNat, Int.cast_ofNat] using UpperHalfPlane.modular_T_zpow_smul z 6
  rw [hact]
  have hdist : dist (z : ℂ) (((6 : ℝ) +ᵥ z : UpperHalfPlane) : ℂ) = 6 := by
    rw [dist_eq_norm]
    have hh : (z : ℂ) - (((6 : ℝ) +ᵥ z : UpperHalfPlane) : ℂ) = (-6 : ℂ) := by
      rw [UpperHalfPlane.coe_vadd]
      norm_num
    rw [hh]
    norm_num
  calc
    _ ≤ dist (z : ℂ) (((6 : ℝ) +ᵥ z : UpperHalfPlane) : ℂ) /
        Real.sqrt (z.im * ((6 : ℝ) +ᵥ z : UpperHalfPlane).im) :=
      UpperHalfPlane.dist_le_dist_coe_div_sqrt _ _
    _ = _ := by rw [hdist, UpperHalfPlane.vadd_im, Real.sqrt_mul_self z.im_pos.le]

/-- The commutator's displacement infimum is zero in the actual hyperbolic
metric; it is approached at increasing height in its conjugate coordinates. -/
theorem paperCuspHolonomy_translationLength_zero :
    hyperbolicTranslationLength (paperCuspHolonomy : SL(2, ℝ)) = 0 := by
  apply le_antisymm ?_ (hyperbolicTranslationLength_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let z : UpperHalfPlane := UpperHalfPlane.mk ⟨0, 6 / ε⟩ (div_pos (by norm_num) hε)
  have hbound := hyperbolicTranslationLength_le_displacement
    (paperCuspHolonomy : SL(2, ℝ)) (ModularGroup.S • z)
  rw [← modularInteger_smul_eq_real, paperCuspHolonomy_smul_S,
    (modularInteger_isometry ModularGroup.S).dist_eq] at hbound
  have h := hbound.trans (modular_T_pow_six_displacement_bound z)
  have heq : 6 / z.im = ε := by
    change 6 / (6 / ε) = ε
    field_simp
  simpa only [heq, zero_add] using h

end Markov
