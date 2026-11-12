import Markov.FareyHolonomy

/-! Four concrete Farey seeds bounding the four quadrants, in counterclockwise
order. Their matrices are actual words in the original generators and their
inverses. Single-coordinate reflections are not asserted to preserve the norm:
the mixed-sign sectors have initial product trace 6, rather than 3. -/

namespace Markov

/-- Counterclockwise boundary directions for the four coordinate quadrants. -/
def quadrantSeedDirections : Fin 4 → (ℤ × ℤ) × (ℤ × ℤ)
  | 0 => ((1, 0), (0, 1))
  | 1 => ((0, 1), (-1, 0))
  | 2 => ((-1, 0), (0, -1))
  | 3 => ((0, -1), (1, 0))

/-- Matrices assigned to those boundary directions. Adjugates are inverses
because the concrete generators have determinant one. -/
def quadrantSeedMatrices : Fin 4 → IntMatrixTwo × IntMatrixTwo
  | 0 => (modularGeneratorA, modularGeneratorB)
  | 1 => (modularGeneratorB, modularGeneratorA.adjugate)
  | 2 => (modularGeneratorA.adjugate, modularGeneratorB.adjugate)
  | 3 => (modularGeneratorB.adjugate, modularGeneratorA)

/-- Every quadrant seed supplies the arithmetic required by the Farey moves. -/
theorem quadrantSeed_positiveFrickePair (k : Fin 4) :
    PositiveFrickePair (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 := by
  fin_cases k <;> constructor <;>
    norm_num [quadrantSeedMatrices, modularGeneratorA, modularGeneratorB,
      Matrix.det_fin_two, Matrix.adjugate_fin_two, Matrix.trace,
      Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two]

/-- All four direction pairs have determinant +1. -/
theorem quadrantSeed_det_eq_one (k : Fin 4) :
    intDet (quadrantSeedDirections k).1 (quadrantSeedDirections k).2 = 1 := by
  fin_cases k <;> norm_num [quadrantSeedDirections, intDet]

/-- The two boundary traces are 3 in every quadrant. Product traces alternate
between 3 and 6, recording the difference between equal and mixed signs. -/
theorem quadrantSeed_trace_triple (k : Fin 4) :
    (quadrantSeedMatrices k).1.trace = 3 ∧
    (quadrantSeedMatrices k).2.trace = 3 ∧
    ((quadrantSeedMatrices k).1 * (quadrantSeedMatrices k).2).trace =
      if (k : ℕ) % 2 = 0 then 3 else 6 := by
  fin_cases k <;>
    norm_num [quadrantSeedMatrices, modularGeneratorA, modularGeneratorB,
      Matrix.adjugate_fin_two, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The actual puncture trace condition holds for each of the four seeds. -/
theorem quadrantSeed_commutator_trace (k : Fin 4) :
    let M := (quadrantSeedMatrices k).1
    let N := (quadrantSeedMatrices k).2
    (M * N * M.adjugate * N.adjugate).trace = -2 := by
  have hp := quadrantSeed_positiveFrickePair k
  have hf := matrix_fricke_polynomial (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
  rw [hp.det_left, hp.det_right] at hf
  dsimp
  linarith [hp.fricke]

end Markov
