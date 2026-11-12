import Markov.FrickeRay
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace

/-! The matrix origin of the Fricke ray recurrence. These theorems apply to
actual determinant-one integer matrices. Their identification with the curves
and norm of the modular punctured torus is not assumed or asserted here. -/

namespace Markov

/-- The two-dimensional characteristic identity, over any commutative ring. -/
theorem matrix_two_characteristic {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) :
    M ^ 2 = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace, Matrix.diag_apply,
      Matrix.det_fin_two, Matrix.smul_apply] <;> ring

/-- Cayley–Hamilton gives the trace recurrence for `M^n N`. -/
theorem matrix_trace_ray_recurrence {R : Type*} [CommRing R]
    (M N : Matrix (Fin 2) (Fin 2) R) (hM : M.det = 1) (n : ℕ) :
    (M ^ (n + 2) * N).trace = M.trace * (M ^ (n + 1) * N).trace -
      (M ^ n * N).trace := by
  have he := matrix_two_characteristic M
  rw [hM, one_smul] at he
  have hm : M ^ (n + 2) * N = M.trace • (M ^ (n + 1) * N) - M ^ n * N := by
    rw [pow_add, he, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      mul_one, pow_succ]
  rw [hm, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]

/-- Every determinant-one integer matrix pair realizes the integer recurrence. -/
theorem matrix_trace_ray_eq_frickeRay (M N : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : M.det = 1) (n : ℕ) :
    (M ^ n * N).trace = frickeRay M.trace N.trace (M * N).trace n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [frickeRay]
  | one => simp [frickeRay]
  | more n hn hn1 =>
    rw [matrix_trace_ray_recurrence M N hM n, hn, hn1, frickeRay]

/-- Polynomial trace identity before specializing either determinant. -/
theorem matrix_fricke_polynomial {R : Type*} [CommRing R]
    (M N : Matrix (Fin 2) (Fin 2) R) :
    M.trace ^ 2 * N.det + N.trace ^ 2 * M.det + (M * N).trace ^ 2 -
      M.trace * N.trace * (M * N).trace =
      (M * N * M.adjugate * N.adjugate).trace + 2 * M.det * N.det := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.det_fin_two, Matrix.adjugate_fin_two]
  ring

/-- A determinant-one pair with parabolic commutator trace -2 supplies the
integer Fricke equation used in Proposition 4. -/
theorem matrix_fricke_of_commutator (M N : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : M.det = 1) (hN : N.det = 1)
    (hc : (M * N * M.adjugate * N.adjugate).trace = -2) :
    M.trace ^ 2 + N.trace ^ 2 + (M * N).trace ^ 2 =
      M.trace * N.trace * (M * N).trace := by
  have h := matrix_fricke_polynomial M N
  rw [hM, hN, hc] at h
  linarith

/-- A concrete integral determinant-one generator of trace 3. -/
def modularGeneratorA : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 1]

def modularGeneratorB : Matrix (Fin 2) (Fin 2) ℤ := !![2, -1; -1, 1]

theorem modular_generators_det_trace :
    modularGeneratorA.det = 1 ∧ modularGeneratorB.det = 1 ∧
      modularGeneratorA.trace = 3 ∧ modularGeneratorB.trace = 3 ∧
      (modularGeneratorA * modularGeneratorB).trace = 3 := by
  norm_num [modularGeneratorA, modularGeneratorB, Matrix.det_fin_two,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two]

/-- The seed pair realizes the actual integral sequence with initial traces 3. -/
theorem modular_generator_ray (n : ℕ) :
    (modularGeneratorA ^ n * modularGeneratorB).trace = frickeRay 3 3 3 n := by
  have h := matrix_trace_ray_eq_frickeRay modularGeneratorA modularGeneratorB
    modular_generators_det_trace.1 n
  simpa only [modular_generators_det_trace.2.2.1, modular_generators_det_trace.2.2.2.1,
    modular_generators_det_trace.2.2.2.2] using h

/-- The commutator of the concrete generators has the puncture trace. -/
theorem modular_generators_commutator_trace :
    (modularGeneratorA * modularGeneratorB * modularGeneratorA.adjugate *
      modularGeneratorB.adjugate).trace = -2 := by
  norm_num [modularGeneratorA, modularGeneratorB, Matrix.adjugate_fin_two,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two]

end Markov
