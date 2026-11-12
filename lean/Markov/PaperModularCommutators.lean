import Markov.ModularTraceQuotient
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.GroupTheory.Commutator.Basic

/-! The original paper seed matrices are actual commutators of the standard
integral modular generators. Their generated subgroup is the trace subgroup
itself, and explicit generator conjugations prove its normality. No index or
geometric identification is asserted here. -/

open scoped MatrixGroups
namespace Markov

/-- The first paper seed, with the library's `g*h*g⁻¹*h⁻¹` convention. -/
theorem paperGeneratorASL_eq_commutator :
    paperGeneratorASL = ⁅ModularGroup.S, ModularGroup.T⁆ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperGeneratorASL, paperGeneratorA, commutatorElement_def,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      ModularGroup.coe_S, ModularGroup.coe_T, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The second paper seed is the corresponding commutator with `T⁻¹`. -/
theorem paperGeneratorBSL_eq_commutator :
    paperGeneratorBSL = ⁅ModularGroup.S, ModularGroup.T⁻¹⁆ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperGeneratorBSL, paperGeneratorB, commutatorElement_def,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      ModularGroup.coe_S, ModularGroup.coe_T, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem modularGeneratorASL_eq_paperGeneratorASL_inv :
    modularGeneratorASL = paperGeneratorASL⁻¹ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularGeneratorASL, modularGeneratorA, paperGeneratorASL,
      paperGeneratorA, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem modularGeneratorBSL_eq_paperGeneratorBSL_inv :
    modularGeneratorBSL = paperGeneratorBSL⁻¹ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularGeneratorBSL, modularGeneratorB, paperGeneratorBSL,
      paperGeneratorB, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem S_conjugates_paperA :
    ModularGroup.S * paperGeneratorASL * ModularGroup.S⁻¹ = paperGeneratorASL⁻¹ := by
  exact paperSeedConjugatorSL_conjugates_paperA.trans
    modularGeneratorASL_eq_paperGeneratorASL_inv

theorem S_conjugates_paperB :
    ModularGroup.S * paperGeneratorBSL * ModularGroup.S⁻¹ = paperGeneratorBSL⁻¹ := by
  exact paperSeedConjugatorSL_conjugates_paperB.trans
    modularGeneratorBSL_eq_paperGeneratorBSL_inv

theorem S_inv_conjugates_paperA :
    ModularGroup.S⁻¹ * paperGeneratorASL * ModularGroup.S = paperGeneratorASL⁻¹ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperGeneratorASL, paperGeneratorA, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_S,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem S_inv_conjugates_paperB :
    ModularGroup.S⁻¹ * paperGeneratorBSL * ModularGroup.S = paperGeneratorBSL⁻¹ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperGeneratorBSL, paperGeneratorB, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_S,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem T_conjugates_paperA :
    ModularGroup.T * paperGeneratorASL * ModularGroup.T⁻¹ =
      paperGeneratorBSL * paperGeneratorASL := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperGeneratorASL, paperGeneratorA, paperGeneratorBSL, paperGeneratorB,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      ModularGroup.coe_T, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem T_conjugates_paperB :
    ModularGroup.T * paperGeneratorBSL * ModularGroup.T⁻¹ = paperGeneratorASL⁻¹ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperGeneratorASL, paperGeneratorA, paperGeneratorBSL, paperGeneratorB,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      ModularGroup.coe_T, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem T_inv_conjugates_paperA :
    ModularGroup.T⁻¹ * paperGeneratorASL * ModularGroup.T = paperGeneratorBSL⁻¹ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperGeneratorASL, paperGeneratorA, paperGeneratorBSL, paperGeneratorB,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      ModularGroup.coe_T, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem T_inv_conjugates_paperB :
    ModularGroup.T⁻¹ * paperGeneratorBSL * ModularGroup.T =
      paperGeneratorASL * paperGeneratorBSL := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperGeneratorASL, paperGeneratorA, paperGeneratorBSL, paperGeneratorB,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      ModularGroup.coe_T, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem paperGeneratorASL_mem_paperTraceSubgroup :
    paperGeneratorASL ∈ paperTraceSubgroup :=
  Subgroup.subset_closure (by simp)

theorem paperGeneratorBSL_mem_paperTraceSubgroup :
    paperGeneratorBSL ∈ paperTraceSubgroup :=
  Subgroup.subset_closure (by simp)

theorem paperTraceSubgroup_le_iff (Γ : Subgroup SL(2, ℤ)) :
    paperTraceSubgroup ≤ Γ ↔ paperGeneratorASL ∈ Γ ∧ paperGeneratorBSL ∈ Γ := by
  constructor
  · intro h
    exact ⟨h paperGeneratorASL_mem_paperTraceSubgroup,
      h paperGeneratorBSL_mem_paperTraceSubgroup⟩
  · intro h
    apply (Subgroup.closure_le Γ).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact h.1
    · exact h.2

/-- Inverting both generators leaves the actual generated subgroup unchanged. -/
theorem paperTraceSubgroup_eq_modularTraceSubgroup :
    paperTraceSubgroup = modularTraceSubgroup := by
  apply le_antisymm
  · apply (paperTraceSubgroup_le_iff _).mpr
    constructor
    · have h := modularTraceSubgroup.inv_mem modularGeneratorASL_mem_modularTraceSubgroup
      rwa [modularGeneratorASL_eq_paperGeneratorASL_inv, inv_inv] at h
    · have h := modularTraceSubgroup.inv_mem modularGeneratorBSL_mem_modularTraceSubgroup
      rwa [modularGeneratorBSL_eq_paperGeneratorBSL_inv, inv_inv] at h
  · apply (modularTraceSubgroup_le_iff _).mpr
    constructor
    · rw [modularGeneratorASL_eq_paperGeneratorASL_inv]
      exact paperTraceSubgroup.inv_mem paperGeneratorASL_mem_paperTraceSubgroup
    · rw [modularGeneratorBSL_eq_paperGeneratorBSL_inv]
      exact paperTraceSubgroup.inv_mem paperGeneratorBSL_mem_paperTraceSubgroup

private theorem paperTraceSubgroup_conjugate_mem (c : SL(2, ℤ))
    (ha : c * paperGeneratorASL * c⁻¹ ∈ paperTraceSubgroup)
    (hb : c * paperGeneratorBSL * c⁻¹ ∈ paperTraceSubgroup)
    (x : SL(2, ℤ)) (hx : x ∈ paperTraceSubgroup) :
    c * x * c⁻¹ ∈ paperTraceSubgroup := by
  have hle : paperTraceSubgroup ≤
      paperTraceSubgroup.comap (MulAut.conj c).toMonoidHom := by
    apply (paperTraceSubgroup_le_iff _).mpr
    exact ⟨ha, hb⟩
  exact hle hx

private theorem paperTraceSubgroup_mem_normalizer (c : SL(2, ℤ))
    (ha : c * paperGeneratorASL * c⁻¹ ∈ paperTraceSubgroup)
    (hb : c * paperGeneratorBSL * c⁻¹ ∈ paperTraceSubgroup)
    (hai : c⁻¹ * paperGeneratorASL * c ∈ paperTraceSubgroup)
    (hbi : c⁻¹ * paperGeneratorBSL * c ∈ paperTraceSubgroup) :
    c ∈ paperTraceSubgroup.normalizer := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact paperTraceSubgroup_conjugate_mem c ha hb x
  · intro hx
    have hh := paperTraceSubgroup_conjugate_mem c⁻¹ (by simpa using hai)
      (by simpa using hbi) (c * x * c⁻¹) hx
    simpa [mul_assoc] using hh

theorem S_mem_paperTraceSubgroup_normalizer :
    ModularGroup.S ∈ paperTraceSubgroup.normalizer := by
  apply paperTraceSubgroup_mem_normalizer
  · rw [S_conjugates_paperA]
    exact paperTraceSubgroup.inv_mem paperGeneratorASL_mem_paperTraceSubgroup
  · rw [S_conjugates_paperB]
    exact paperTraceSubgroup.inv_mem paperGeneratorBSL_mem_paperTraceSubgroup
  · rw [S_inv_conjugates_paperA]
    exact paperTraceSubgroup.inv_mem paperGeneratorASL_mem_paperTraceSubgroup
  · rw [S_inv_conjugates_paperB]
    exact paperTraceSubgroup.inv_mem paperGeneratorBSL_mem_paperTraceSubgroup

theorem T_mem_paperTraceSubgroup_normalizer :
    ModularGroup.T ∈ paperTraceSubgroup.normalizer := by
  apply paperTraceSubgroup_mem_normalizer
  · rw [T_conjugates_paperA]
    exact paperTraceSubgroup.mul_mem paperGeneratorBSL_mem_paperTraceSubgroup
      paperGeneratorASL_mem_paperTraceSubgroup
  · rw [T_conjugates_paperB]
    exact paperTraceSubgroup.inv_mem paperGeneratorASL_mem_paperTraceSubgroup
  · rw [T_inv_conjugates_paperA]
    exact paperTraceSubgroup.inv_mem paperGeneratorBSL_mem_paperTraceSubgroup
  · rw [T_inv_conjugates_paperB]
    exact paperTraceSubgroup.mul_mem paperGeneratorASL_mem_paperTraceSubgroup
      paperGeneratorBSL_mem_paperTraceSubgroup

instance paperTraceSubgroup_normal : paperTraceSubgroup.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← SpecialLinearGroup.SL2Z_generators]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact S_mem_paperTraceSubgroup_normalizer
  · exact T_mem_paperTraceSubgroup_normalizer

/-- Actual normality follows from the proved standard-generator conjugations. -/
instance modularTraceSubgroup_normal : modularTraceSubgroup.Normal := by
  rw [← paperTraceSubgroup_eq_modularTraceSubgroup]
  infer_instance

end Markov
