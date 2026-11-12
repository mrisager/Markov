import Markov.PaperSeeds
import Mathlib.Algebra.Group.End

/-! The determinant-one simultaneous conjugacy from the paper's two seed
matrices to the trace construction's seeds, preserving the generator labels.
The paper matrices and their determinant and trace calculations are reused
from `PaperSeeds`. This module proves matrix and group identities only. -/

namespace Markov

/-- The standard determinant-one quarter-turn matrix. -/
def paperSeedConjugator : IntMatrixTwo := !![0, -1; 1, 0]

theorem paperSeedConjugator_det : paperSeedConjugator.det = 1 := by
  norm_num [paperSeedConjugator, Matrix.det_fin_two]

theorem paperSeedConjugator_mul_adjugate :
    paperSeedConjugator * paperSeedConjugator.adjugate = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperSeedConjugator, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem paperSeedConjugator_adjugate_mul :
    paperSeedConjugator.adjugate * paperSeedConjugator = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperSeedConjugator, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- This orientation-preserving conjugacy preserves the first seed's label. -/
theorem paperSeedConjugator_conjugates_paperA :
    paperSeedConjugator * paperGeneratorA * paperSeedConjugator.adjugate =
      modularGeneratorA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperSeedConjugator, paperGeneratorA, modularGeneratorA,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- The same conjugacy preserves the second seed's label. -/
theorem paperSeedConjugator_conjugates_paperB :
    paperSeedConjugator * paperGeneratorB * paperSeedConjugator.adjugate =
      modularGeneratorB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperSeedConjugator, paperGeneratorB, modularGeneratorB,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem paperSeedConjugator_inverse_conjugates_modularA :
    paperSeedConjugator.adjugate * modularGeneratorA * paperSeedConjugator =
      paperGeneratorA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperSeedConjugator, paperGeneratorA, modularGeneratorA,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem paperSeedConjugator_inverse_conjugates_modularB :
    paperSeedConjugator.adjugate * modularGeneratorB * paperSeedConjugator =
      paperGeneratorB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperSeedConjugator, paperGeneratorB, modularGeneratorB,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem paperSeedConjugator_trace_conjugate (M : IntMatrixTwo) :
    (paperSeedConjugator * M * paperSeedConjugator.adjugate).trace = M.trace := by
  rw [Matrix.trace_mul_cycle, paperSeedConjugator_adjugate_mul, one_mul]

theorem paperSeedConjugator_trace_inverse_conjugate (M : IntMatrixTwo) :
    (paperSeedConjugator.adjugate * M * paperSeedConjugator).trace = M.trace := by
  rw [Matrix.trace_mul_cycle, paperSeedConjugator_mul_adjugate, one_mul]

/-- The paper's first seed as an actual integral special-linear element. -/
def paperGeneratorASL : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨paperGeneratorA, paper_generators_det_trace.1⟩

/-- The paper's second seed as an actual integral special-linear element. -/
def paperGeneratorBSL : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨paperGeneratorB, paper_generators_det_trace.2.1⟩

/-- The trace construction's first seed as a special-linear element. -/
def modularGeneratorASL : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨modularGeneratorA, modular_generators_det_trace.1⟩

/-- The trace construction's second seed as a special-linear element. -/
def modularGeneratorBSL : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨modularGeneratorB, modular_generators_det_trace.2.1⟩

/-- The conjugator is the standard modular special-linear element `S`. -/
def paperSeedConjugatorSL : Matrix.SpecialLinearGroup (Fin 2) ℤ := ModularGroup.S

@[simp] theorem coe_paperGeneratorASL :
    (paperGeneratorASL : IntMatrixTwo) = paperGeneratorA := rfl

@[simp] theorem coe_paperGeneratorBSL :
    (paperGeneratorBSL : IntMatrixTwo) = paperGeneratorB := rfl

@[simp] theorem coe_modularGeneratorASL :
    (modularGeneratorASL : IntMatrixTwo) = modularGeneratorA := rfl

@[simp] theorem coe_modularGeneratorBSL :
    (modularGeneratorBSL : IntMatrixTwo) = modularGeneratorB := rfl

@[simp] theorem coe_paperSeedConjugatorSL :
    (paperSeedConjugatorSL : IntMatrixTwo) = paperSeedConjugator := rfl

theorem paperSeedConjugatorSL_conjugates_paperA :
    paperSeedConjugatorSL * paperGeneratorASL * paperSeedConjugatorSL⁻¹ =
      modularGeneratorASL := by
  apply Subtype.ext
  exact paperSeedConjugator_conjugates_paperA

theorem paperSeedConjugatorSL_conjugates_paperB :
    paperSeedConjugatorSL * paperGeneratorBSL * paperSeedConjugatorSL⁻¹ =
      modularGeneratorBSL := by
  apply Subtype.ext
  exact paperSeedConjugator_conjugates_paperB

theorem paperSeedConjugatorSL_inverse_conjugates_modularA :
    paperSeedConjugatorSL⁻¹ * modularGeneratorASL * paperSeedConjugatorSL =
      paperGeneratorASL := by
  apply Subtype.ext
  exact paperSeedConjugator_inverse_conjugates_modularA

theorem paperSeedConjugatorSL_inverse_conjugates_modularB :
    paperSeedConjugatorSL⁻¹ * modularGeneratorBSL * paperSeedConjugatorSL =
      paperGeneratorBSL := by
  apply Subtype.ext
  exact paperSeedConjugator_inverse_conjugates_modularB

/-- The resulting automorphism transports arbitrary words and inverses. -/
def paperSeedConjugation :
    Matrix.SpecialLinearGroup (Fin 2) ℤ ≃* Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  MulAut.conj paperSeedConjugatorSL

theorem paperSeedConjugation_apply (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    paperSeedConjugation g = paperSeedConjugatorSL * g * paperSeedConjugatorSL⁻¹ :=
  rfl

@[simp] theorem paperSeedConjugation_paperA :
    paperSeedConjugation paperGeneratorASL = modularGeneratorASL :=
  paperSeedConjugatorSL_conjugates_paperA

@[simp] theorem paperSeedConjugation_paperB :
    paperSeedConjugation paperGeneratorBSL = modularGeneratorBSL :=
  paperSeedConjugatorSL_conjugates_paperB

@[simp] theorem paperSeedConjugation_symm_modularA :
    paperSeedConjugation.symm modularGeneratorASL = paperGeneratorASL := by
  rw [← paperSeedConjugation_paperA, MulEquiv.symm_apply_apply]

@[simp] theorem paperSeedConjugation_symm_modularB :
    paperSeedConjugation.symm modularGeneratorBSL = paperGeneratorBSL := by
  rw [← paperSeedConjugation_paperB, MulEquiv.symm_apply_apply]

/-- Trace is preserved for every special-linear word, including inverses. -/
theorem paperSeedConjugation_trace (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (paperSeedConjugation g : IntMatrixTwo).trace = (g : IntMatrixTwo).trace := by
  exact paperSeedConjugator_trace_conjugate (g : IntMatrixTwo)

end Markov
