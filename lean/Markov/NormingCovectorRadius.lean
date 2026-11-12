import Markov.ShortNormalArc

/-! A uniform positive lower radius for the Euclidean coordinates of
actual trace norming supports, and the resulting normalization estimate. -/

noncomputable section
open scoped RealInnerProductSpace

namespace Markov

/-- Functional evaluation is the Euclidean pairing between dual and
primal coordinates in the fixed trace basis. -/
theorem traceSupport_eval_eq_inner_coordinates (f : StrongDual ℝ TracePlane)
    (x : TracePlane) :
    f x = ⟪euclideanDualCoordinates traceBasis f, traceEuclideanCoordinates x⟫ := by
  have hrepr := congrArg f (traceBasis.sum_equivFun x)
  simp only [Fin.sum_univ_two] at hrepr
  simpa [Fin.sum_univ_two, PiLp.inner_apply, traceEuclideanCoordinates_apply,
    real_inner_comm, mul_comm] using hrepr.symm

/-- A fixed positive radius that works for every genuine norming covector
at a nonzero point of the trace plane. -/
def traceNormingCovectorRadius : ℝ := 1 / (‖traceEuclideanCoordinates‖ + 1)

theorem traceNormingCovectorRadius_pos : 0 < traceNormingCovectorRadius := by
  unfold traceNormingCovectorRadius
  positivity

theorem traceNormingCovectorRadius_le (x : TracePlane) (hx : x ≠ 0)
    (f : StrongDual ℝ TracePlane) (hf : f ∈ normingFunctionals x) :
    traceNormingCovectorRadius ≤ ‖euclideanDualCoordinates traceBasis f‖ := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hC : 0 < ‖traceEuclideanCoordinates‖ + 1 := by positivity
  have hcoord : ‖traceEuclideanCoordinates x‖ ≤
      (‖traceEuclideanCoordinates‖ + 1) * ‖x‖ := by
    apply (traceEuclideanCoordinates.le_opNorm x).trans
    nlinarith [norm_nonneg x]
  have heval : ‖x‖ ≤ ‖euclideanDualCoordinates traceBasis f‖ *
      ‖traceEuclideanCoordinates x‖ := by
    rw [← hf.2, traceSupport_eval_eq_inner_coordinates]
    exact real_inner_le_norm _ _
  have hbound : ‖x‖ ≤
      (‖euclideanDualCoordinates traceBasis f‖ * (‖traceEuclideanCoordinates‖ + 1)) * ‖x‖ := by
    calc
      ‖x‖ ≤ ‖euclideanDualCoordinates traceBasis f‖ * ‖traceEuclideanCoordinates x‖ := heval
      _ ≤ ‖euclideanDualCoordinates traceBasis f‖ *
          ((‖traceEuclideanCoordinates‖ + 1) * ‖x‖) :=
        mul_le_mul_of_nonneg_left hcoord (norm_nonneg _)
      _ = _ := by ring
  have hone : 1 ≤ ‖euclideanDualCoordinates traceBasis f‖ *
      (‖traceEuclideanCoordinates‖ + 1) := by nlinarith
  unfold traceNormingCovectorRadius
  exact (div_le_iff₀ hC).mpr hone

/-- Existence form of the uniform lower radius for every actual support
over every nonzero point. -/
theorem exists_traceNormingCovectorRadius :
    ∃ r : ℝ, 0 < r ∧ ∀ x : TracePlane, x ≠ 0 →
      ∀ f : StrongDual ℝ TracePlane, f ∈ normingFunctionals x →
        r ≤ ‖euclideanDualCoordinates traceBasis f‖ :=
  ⟨traceNormingCovectorRadius, traceNormingCovectorRadius_pos, traceNormingCovectorRadius_le⟩

/-- Actual norming covectors over arbitrary nonzero points satisfy one
uniform normalization distance estimate. -/
theorem traceNormingCovector_normalize_dist_le
    (x y : TracePlane) (hx : x ≠ 0) (hy : y ≠ 0)
    (f g : StrongDual ℝ TracePlane)
    (hf : f ∈ normingFunctionals x) (hg : g ∈ normingFunctionals y) :
    dist (normalizedEuclideanCovector traceBasis f) (normalizedEuclideanCovector traceBasis g) ≤
      (2 / traceNormingCovectorRadius) *
        dist (euclideanDualCoordinates traceBasis f) (euclideanDualCoordinates traceBasis g) := by
  exact normalizedEuclideanCovector_dist_le_of_norm_lower_bound traceBasis f g
    traceNormingCovectorRadius traceNormingCovectorRadius_pos
    (traceNormingCovectorRadius_le x hx f hf) (traceNormingCovectorRadius_le y hy g hg)

theorem exists_traceNormingCovectorNormalizationConstant :
    ∃ K : ℝ, 0 < K ∧ ∀ x y : TracePlane, x ≠ 0 → y ≠ 0 →
      ∀ f g : StrongDual ℝ TracePlane, f ∈ normingFunctionals x → g ∈ normingFunctionals y →
        dist (normalizedEuclideanCovector traceBasis f) (normalizedEuclideanCovector traceBasis g) ≤
          K * dist (euclideanDualCoordinates traceBasis f) (euclideanDualCoordinates traceBasis g) :=
  ⟨2 / traceNormingCovectorRadius, div_pos (by norm_num) traceNormingCovectorRadius_pos,
    traceNormingCovector_normalize_dist_le⟩

end Markov
