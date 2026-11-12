import Markov.NormalDeterminant
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! Measure-preserving pair coordinates for the standard Euclidean plane. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace Markov

/-- The coordinate-pair identification with the standard Euclidean plane. -/
def euclideanPairEquiv : (ℝ × ℝ) ≃ᵐ EuclideanSpace ℝ (Fin 2) :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

/-- The same coordinate map bundled as a continuous linear equivalence. -/
def euclideanPairContinuousLinearEquiv : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((LinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm).toContinuousLinearEquiv

@[simp] theorem euclideanPairEquiv_apply (p : ℝ × ℝ) :
    euclideanPairEquiv p = WithLp.toLp 2 ![p.1, p.2] := rfl

@[simp] theorem euclideanPairContinuousLinearEquiv_apply (p : ℝ × ℝ) :
    euclideanPairContinuousLinearEquiv p = euclideanPairEquiv p := rfl

@[simp] theorem euclideanPairEquiv_apply_zero (p : ℝ × ℝ) :
    euclideanPairEquiv p 0 = p.1 := rfl

@[simp] theorem euclideanPairEquiv_apply_one (p : ℝ × ℝ) :
    euclideanPairEquiv p 1 = p.2 := rfl

@[simp] theorem euclideanPairEquiv_symm_apply (x : EuclideanSpace ℝ (Fin 2)) :
    euclideanPairEquiv.symm x = (x 0, x 1) := rfl

@[simp] theorem euclideanPairEquiv_int (n : ℤ × ℤ) :
    euclideanPairEquiv ((n.1 : ℝ), (n.2 : ℝ)) = euclideanIntDirection n := rfl

/-- Coordinate pairs and Euclidean coordinates carry precisely the same Lebesgue measure. -/
theorem euclideanPairEquiv_measurePreserving : MeasurePreserving euclideanPairEquiv :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm

theorem euclideanPairEquiv_continuous : Continuous euclideanPairEquiv :=
  euclideanPairContinuousLinearEquiv.continuous

theorem euclideanPairEquiv_symm_continuous : Continuous euclideanPairEquiv.symm :=
  euclideanPairContinuousLinearEquiv.symm.continuous

theorem euclideanPairEquiv_contDiff : ContDiff ℝ ∞ euclideanPairEquiv :=
  euclideanPairContinuousLinearEquiv.contDiff

theorem euclideanPairEquiv_symm_contDiff : ContDiff ℝ ∞ euclideanPairEquiv.symm :=
  euclideanPairContinuousLinearEquiv.symm.contDiff

theorem euclideanPairEquiv_isClosedEmbedding : Topology.IsClosedEmbedding euclideanPairEquiv :=
  euclideanPairContinuousLinearEquiv.toHomeomorph.isClosedEmbedding

theorem euclideanPairEquiv_norm_sq (p : ℝ × ℝ) :
    ‖euclideanPairEquiv p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs]

theorem euclideanPairEquiv_inner (p q : ℝ × ℝ) :
    inner ℝ (euclideanPairEquiv p) (euclideanPairEquiv q) = p.1 * q.1 + p.2 * q.2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, mul_comm]

/-- The two-dimensional Fourier phase is the product of the two one-dimensional phases. -/
theorem euclideanPairEquiv_fourier_phase (p q : ℝ × ℝ) :
    Complex.exp ((↑(-2 * Real.pi * inner ℝ (euclideanPairEquiv p)
      (euclideanPairEquiv q)) : ℂ) * Complex.I) =
    Complex.exp ((↑(-2 * Real.pi * p.1 * q.1) : ℂ) * Complex.I) *
      Complex.exp ((↑(-2 * Real.pi * p.2 * q.2) : ℂ) * Complex.I) := by
  rw [euclideanPairEquiv_inner, ← Complex.exp_add]
  congr 1
  push_cast
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integration over the Euclidean plane in standard coordinate pairs. -/
theorem integral_euclidean_eq_integral_pair (f : EuclideanSpace ℝ (Fin 2) → E) :
    (∫ z, f z) = ∫ p : ℝ × ℝ, f (euclideanPairEquiv p) :=
  (euclideanPairEquiv_measurePreserving.integral_comp' f).symm

/-- Fubini's identity in the standard Euclidean coordinates, with no normalization factor. -/
theorem integral_euclidean_eq_integral_integral (f : EuclideanSpace ℝ (Fin 2) → E)
    (hf : Integrable f) :
    (∫ z, f z) = ∫ x : ℝ, ∫ y : ℝ, f (euclideanPairEquiv (x, y)) := by
  rw [integral_euclidean_eq_integral_pair]
  apply integral_prod
  exact (euclideanPairEquiv_measurePreserving.integrable_comp_emb
    euclideanPairEquiv.measurableEmbedding).mpr hf

end Markov
