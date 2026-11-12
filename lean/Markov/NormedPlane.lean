import Markov.NormSupport
import Markov.TraceLengthBounds
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! Coordinate realization of the selected supporting functional in
an arbitrary real normed plane. -/

noncomputable section

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def intVector (B : Module.Basis (Fin 2) ℝ E) (u : ℤ × ℤ) : E :=
  (u.1 : ℝ) • B 0 + (u.2 : ℝ) • B 1

def integerColumnMatrix (u v : ℤ × ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(u.1 : ℝ), (v.1 : ℝ); (u.2 : ℝ), (v.2 : ℝ)]

theorem integerColumnMatrix_det (u v : ℤ × ℤ) :
    (integerColumnMatrix u v).det = (intDet u v : ℝ) := by
  simp [integerColumnMatrix, Matrix.det_fin_two, intDet]
  ring

def intPairBasis (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ) (hdet : intDet u v ≠ 0) :
    Module.Basis (Fin 2) ℝ E :=
  B.map (Matrix.toLinearEquiv B (integerColumnMatrix u v)
    (isUnit_iff_ne_zero.mpr (by rw [integerColumnMatrix_det]; exact_mod_cast hdet)))

theorem intPairBasis_zero (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ)
    (hdet : intDet u v ≠ 0) : intPairBasis B u v hdet 0 = intVector B u := by
  simp [intPairBasis, Module.Basis.map_apply, Matrix.toLinearEquiv_apply,
    Matrix.toLin_apply, integerColumnMatrix, intVector, Fin.sum_univ_two,
    Matrix.vecHead, Matrix.vecTail]

theorem intPairBasis_one (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ)
    (hdet : intDet u v ≠ 0) : intPairBasis B u v hdet 1 = intVector B v := by
  simp [intPairBasis, Module.Basis.map_apply, Matrix.toLinearEquiv_apply,
    Matrix.toLin_apply, integerColumnMatrix, intVector, Fin.sum_univ_two,
    Matrix.vecHead, Matrix.vecTail]

def selectedSupportAt (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ) : StrongDual ℝ E :=
  if hdet : intDet u v ≠ 0 then selectedSupport (intPairBasis B u v hdet) else 0

theorem selectedSupportAt_spec (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ)
    (hdet : intDet u v ≠ 0) :
    IsSelectedSupport (intVector B u) (intVector B v) (selectedSupportAt B u v) := by
  rw [selectedSupportAt, dif_pos hdet]
  simpa only [intPairBasis_zero, intPairBasis_one] using selectedSupport_spec (intPairBasis B u v hdet)

def dualCoordinates (B : Module.Basis (Fin 2) ℝ E) (f : StrongDual ℝ E) : ℝ × ℝ :=
  (f (B 0), f (B 1))

theorem dualCoordinates_eval (B : Module.Basis (Fin 2) ℝ E) (f : StrongDual ℝ E) (u : ℤ × ℤ) :
    realCovectorEval (dualCoordinates B f) u = f (intVector B u) := by
  simp [dualCoordinates, realCovectorEval, intVector, mul_comm]

/-- A uniform norm-comparison constant from a fixed coordinate basis. -/
theorem intVector_norm_le (B : Module.Basis (Fin 2) ℝ E) (u : ℤ × ℤ) :
    ‖intVector B u‖ ≤ (‖B 0‖ + ‖B 1‖) * intEuclidean u := by
  have hc := intEuclidean_coordinate_bounds u
  calc
    ‖intVector B u‖ ≤ ‖(u.1 : ℝ) • B 0‖ + ‖(u.2 : ℝ) • B 1‖ := norm_add_le _ _
    _ = |(u.1 : ℝ)| * ‖B 0‖ + |(u.2 : ℝ)| * ‖B 1‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ intEuclidean u * ‖B 0‖ + intEuclidean u * ‖B 1‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hc.1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hc.2 (norm_nonneg _))
    _ = _ := by ring

theorem selectedSupportAt_value_self (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ)
    (hdet : intDet u v ≠ 0) :
    selectedSupportAt B u v (intVector B u) = ‖intVector B u‖ :=
  (selectedSupportAt_spec B u v hdet).1.2

end Markov
