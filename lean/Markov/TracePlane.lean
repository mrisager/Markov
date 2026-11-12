import Markov.TraceNorm
import Markov.SeededSeparation
import Markov.QuadrantCoverage

/-! A concrete real normed plane carrying the constructed algebraic trace
norm. No identification with a geometric surface norm is asserted. -/

noncomputable section
namespace Markov

/-- The real coordinate plane, with the norm constructed from matrix traces. -/
def TracePlane := Fin 2 → ℝ

instance : AddCommGroup TracePlane := inferInstanceAs (AddCommGroup (Fin 2 → ℝ))
instance : Module ℝ TracePlane := inferInstanceAs (Module ℝ (Fin 2 → ℝ))

def traceBasis : Module.Basis (Fin 2) ℝ TracePlane := Pi.basisFun ℝ (Fin 2)

instance : NormedAddCommGroup TracePlane :=
  (traceGroupNorm traceBasis).toNormedAddCommGroup

theorem tracePlane_norm (x : TracePlane) : ‖x‖ = traceGroupNorm traceBasis x := rfl

instance : NormedSpace ℝ TracePlane where
  norm_smul_le a x := by
    change traceGroupNorm traceBasis (a • x) ≤ ‖a‖ * traceGroupNorm traceBasis x
    rw [traceGroupNorm_smul, Real.norm_eq_abs]

/-- Exact primitive interpolation in the positive quadrant. -/
theorem norm_intVector_positive (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    ‖intVector traceBasis p‖ = primitiveSeedLength modularGeneratorA modularGeneratorB p hp := by
  exact traceGroupNorm_positive traceBasis p hp

/-- Exact primitive interpolation in the next quadrant, using its own seed. -/
theorem norm_intVector_next (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    ‖(p.1 : ℝ) • traceBasis 1 + (p.2 : ℝ) • (-traceBasis 0)‖ =
      primitiveSeedLength modularGeneratorB modularGeneratorA.adjugate p hp := by
  exact traceGroupNorm_next traceBasis p hp

/-- The same mixed-sign interpolation expressed in the original coordinates. -/
theorem norm_intVector_quadrant_one (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates 1 p)) :
    ‖intVector traceBasis p‖ =
      primitiveSeedLength modularGeneratorB modularGeneratorA.adjugate (quadrantCoordinates 1 p) hp := by
  have he : intVector traceBasis p = ((quadrantCoordinates 1 p).1 : ℝ) • traceBasis 1 +
      ((quadrantCoordinates 1 p).2 : ℝ) • (-traceBasis 0) := by
    simp only [intVector, quadrantCoordinates, Int.cast_neg]
    module
  rw [he]
  exact norm_intVector_next (quadrantCoordinates 1 p) hp

@[simp] theorem norm_traceBasis_zero : ‖traceBasis 0‖ = traceAxisLength :=
  traceGroupNorm_basis_zero traceBasis

@[simp] theorem norm_traceBasis_one : ‖traceBasis 1‖ = traceAxisLength :=
  traceGroupNorm_basis_one traceBasis

@[simp] theorem norm_traceBasis_sum : ‖traceBasis 0 + traceBasis 1‖ = traceAxisLength :=
  traceGroupNorm_basis_sum traceBasis

end Markov
