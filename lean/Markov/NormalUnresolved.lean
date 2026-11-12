import Markov.NormalArcProximity
import Markov.NormalDeterminant

/-! Conditional height and arc estimates from actual local boundary normals.
The diameter of the actual normal set, a nearby actual normal, and its
exponentially small error remain explicit hypotheses. These give the
determinant upper estimate rather than assuming it. No normal-turn tail
or association with a global cutoff-sector arc is asserted here. -/

noncomputable section
namespace Markov

/-- A unimodular integral pair determines a genuine plane basis. -/
theorem intDet_ne_zero_of_abs_eq_one {u v : ℤ × ℤ}
    (hdet : |intDet u v| = 1) : intDet u v ≠ 0 := by
  intro hz
  simp [hz] at hdet

/-- The determinant coefficient obtained from the two normal proximity
constants, enlarged to satisfy the logarithmic height estimate. -/
def traceNormalArcDetConstant (M N : ℝ) : ℝ :=
  max 1 ((2 * traceAxisLength) * (M + N))

theorem one_le_traceNormalArcDetConstant (M N : ℝ) :
    1 ≤ traceNormalArcDetConstant M N := le_max_left _ _

/-- A diameter bound and one nearby actual normal control the selected
endpoint support of the same actual local boundary arc. -/
theorem trace_selectedSupportAt_normal_proximity_of_local_arc
    (u v d : ℤ × ℤ) (hdet : intDet u v ≠ 0)
    (ε M N c H η : ℝ) (hε : 0 < ε)
    (hdiam : Metric.diam (normalsOn traceBasis
      (slopeBoundaryArc (intPairBasis traceBasis u v hdet) 0 ε)) ≤
      M * Real.exp (-c * H))
    (hnear : ∃ y ∈ normalsOn traceBasis
      (slopeBoundaryArc (intPairBasis traceBasis u v hdet) 0 ε),
      dist y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * H)) :
    dist (normalizedEuclideanCovector traceBasis (selectedSupportAt traceBasis u v))
      (NormedSpace.normalize (euclideanIntDirection d)) ≤
      (M + N) * Real.exp (-c * H) := by
  apply (selectedSupportAt_normal_dist_le_add traceBasis traceBasis u v hdet ε hε
    (NormedSpace.normalize (euclideanIntDirection d)) (M * Real.exp (-c * H)) η
    hdiam hnear).trans
  calc
    M * Real.exp (-c * H) + η ≤
        M * Real.exp (-c * H) + N * Real.exp (-c * H) := add_le_add le_rfl hη
    _ = (M + N) * Real.exp (-c * H) := by ring

/-- The determinant upper estimate follows from the displayed actual
normal-set hypotheses, with no determinant upper estimate as an input. -/
theorem trace_selectedSupportAt_det_upper_of_local_normal_arc
    (u v d : ℤ × ℤ) (hdet : intDet u v ≠ 0) (hd : d ≠ (0, 0))
    (ε M N c H η : ℝ) (hε : 0 < ε)
    (hdiam : Metric.diam (normalsOn traceBasis
      (slopeBoundaryArc (intPairBasis traceBasis u v hdet) 0 ε)) ≤
      M * Real.exp (-c * H))
    (hnear : ∃ y ∈ normalsOn traceBasis
      (slopeBoundaryArc (intPairBasis traceBasis u v hdet) 0 ε),
      dist y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * H)) :
    |integralCovectorDet
      (dualCoordinates traceBasis (selectedSupportAt traceBasis u v)) d| ≤
      traceNormalArcDetConstant M N * intEuclidean d * Real.exp (-c * H) := by
  have hproximity := trace_selectedSupportAt_normal_proximity_of_local_arc
    u v d hdet ε M N c H η hε hdiam hnear hη
  have hupper := selectedSupportAt_det_upper_of_normal_proximity traceBasis
    u v d hdet hd (M + N) c H hproximity
  rw [norm_traceBasis_zero, norm_traceBasis_one] at hupper
  apply hupper.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_right _ (intEuclidean_nonneg d)
  calc
    (traceAxisLength + traceAxisLength) * (M + N) =
        (2 * traceAxisLength) * (M + N) := by ring
    _ ≤ traceNormalArcDetConstant M N := le_max_right _ _

/-- The endpoint-height part of v1 Lemma 6 under diameter and
nearby-normal estimates for the local boundary arc. -/
theorem trace_unresolved_direction_height_of_local_normal_arc
    (u v d : ℤ × ℤ) (A ε M N c H η : ℝ)
    (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hdet : |intDet u v| = 1)
    (hd : d ≠ (0, 0)) (hε : 0 < ε) (hc : 0 < c)
    (hdiam : Metric.diam (normalsOn traceBasis
      (slopeBoundaryArc
        (intPairBasis traceBasis u v (intDet_ne_zero_of_abs_eq_one hdet)) 0 ε)) ≤
      M * Real.exp (-c * H))
    (hnear : ∃ y ∈ normalsOn traceBasis
      (slopeBoundaryArc
        (intPairBasis traceBasis u v (intDet_ne_zero_of_abs_eq_one hdet)) 0 ε),
      dist y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * H)) :
    0 < (traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c ∧
      H ≤ ((traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c) *
        intEuclidean d * A ^ 2 := by
  exact trace_unresolved_direction_height u v d A (traceNormalArcDetConstant M N) c H
    hA hu hdet hd (one_le_traceNormalArcDetConstant M N) hc
    (trace_selectedSupportAt_det_upper_of_local_normal_arc u v d
      (intDet_ne_zero_of_abs_eq_one hdet) hd ε M N c H η hε hdiam hnear hη)

/-- The corresponding unresolved arc scale, retaining the explicit
comparison `s ≤ C / (H * A)` in addition to the actual local normal inputs.
This does not assert a global cutoff-sector arc association. -/
theorem trace_unresolved_direction_arc_bound_of_local_normal_arc
    (u v d : ℤ × ℤ) (A ε M N c H η C s : ℝ)
    (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hdet : |intDet u v| = 1)
    (hd : d ≠ (0, 0)) (hε : 0 < ε) (hc : 0 < c)
    (hH : 0 < H) (hC : 0 ≤ C) (hs0 : 0 ≤ s)
    (hdiam : Metric.diam (normalsOn traceBasis
      (slopeBoundaryArc
        (intPairBasis traceBasis u v (intDet_ne_zero_of_abs_eq_one hdet)) 0 ε)) ≤
      M * Real.exp (-c * H))
    (hnear : ∃ y ∈ normalsOn traceBasis
      (slopeBoundaryArc
        (intPairBasis traceBasis u v (intDet_ne_zero_of_abs_eq_one hdet)) 0 ε),
      dist y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * H)) (hs : s ≤ C / (H * A)) :
    s ≤ C * Real.sqrt
        ((traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c) *
      Real.sqrt (intEuclidean d) / (H * Real.sqrt H) := by
  exact trace_unresolved_direction_arc_bound u v d A (traceNormalArcDetConstant M N)
    c H C s hA hu hdet hd (one_le_traceNormalArcDetConstant M N) hc hH hC hs0
    (trace_selectedSupportAt_det_upper_of_local_normal_arc u v d
      (intDet_ne_zero_of_abs_eq_one hdet) hd ε M N c H η hε hdiam hnear hη) hs

end Markov
