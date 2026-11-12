import Markov.FareyHolonomy

/-! An algebraic comparison with the two matrices in equation (9) of the
paper's first arXiv version. Swapping matrix coordinates simultaneously
conjugates those matrices to our generators, with their labels exchanged.
This checks the matrix and basis conventions; it makes no identification
of a quotient surface or of its geometric norm. -/

namespace Markov

/-- The first generator displayed in the paper's equation (9). -/
def paperGeneratorA : IntMatrixTwo := !![1, -1; -1, 2]

/-- The second generator displayed in the paper's equation (9). -/
def paperGeneratorB : IntMatrixTwo := !![1, 1; 1, 2]

/-- The matrix interchanging the two matrix-coordinate axes. -/
def seedSwapMatrix : IntMatrixTwo := !![0, 1; 1, 0]

theorem seedSwapMatrix_sq : seedSwapMatrix ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seedSwapMatrix, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem seedSwapMatrix_det_trace :
    seedSwapMatrix.det = -1 ∧ seedSwapMatrix.trace = 0 := by
  norm_num [seedSwapMatrix, Matrix.det_fin_two, Matrix.trace, Matrix.diag_apply]

/-- Simultaneous conjugation sends the paper's first generator to our
second generator, recording the exchange of generator labels. -/
theorem seedSwapMatrix_conjugates_paperA :
    seedSwapMatrix * paperGeneratorA * seedSwapMatrix = modularGeneratorB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seedSwapMatrix, paperGeneratorA, modularGeneratorB,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The same conjugation sends the paper's second generator to our first. -/
theorem seedSwapMatrix_conjugates_paperB :
    seedSwapMatrix * paperGeneratorB * seedSwapMatrix = modularGeneratorA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [seedSwapMatrix, paperGeneratorB, modularGeneratorA,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Both paper matrices have determinant one and the same initial trace
triple as the generators used in the Farey construction. -/
theorem paper_generators_det_trace :
    paperGeneratorA.det = 1 ∧ paperGeneratorB.det = 1 ∧
      paperGeneratorA.trace = 3 ∧ paperGeneratorB.trace = 3 ∧
      (paperGeneratorA * paperGeneratorB).trace = 3 := by
  norm_num [paperGeneratorA, paperGeneratorB, Matrix.det_fin_two,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two]

/-- The paper matrices satisfy the actual puncture commutator trace
identity, with adjugates representing their determinant-one inverses. -/
theorem paper_generators_commutator_trace :
    (paperGeneratorA * paperGeneratorB * paperGeneratorA.adjugate *
      paperGeneratorB.adjugate).trace = -2 := by
  norm_num [paperGeneratorA, paperGeneratorB, Matrix.adjugate_fin_two,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two]

end Markov
