import Markov.NormalUnresolved

/-! Transfer from a local endpoint boundary wedge to a larger actual set.
The nearby normal may occur anywhere over the larger set. Its diameter
bound, proximity witness, and inclusion of a local boundary wedge remain
explicit geometric hypotheses. No normal-turn tail or full Lemma 6 is
asserted here. -/

noncomputable section
open Set

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The selected endpoint normal lies in the closure of the normals over
any actual set containing its local open boundary wedge. -/
theorem selectedSupportAt_normal_mem_closure_normalsOn_of_local_arc_subset
    (B C : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ) (hdet : intDet u v ≠ 0)
    (S : Set E) (ε : ℝ) (hε : 0 < ε)
    (hsubset : slopeBoundaryArc (intPairBasis B u v hdet) 0 ε ⊆ S) :
    normalizedEuclideanCovector C (selectedSupportAt B u v) ∈
      closure (normalsOn C S) := by
  exact (closure_mono (normalsOn_mono C hsubset))
    (selectedSupportAt_normal_mem_closure_normalsOn_slopeBoundaryArc B C u v hdet ε hε)

/-- Diameter and proximity estimates on a larger actual normal set
control the selected endpoint support of a contained local boundary arc. -/
theorem selectedSupportAt_normal_dist_le_add_of_local_arc_subset
    (B C : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ) (hdet : intDet u v ≠ 0)
    (S : Set E) (ε : ℝ) (hε : 0 < ε)
    (hsubset : slopeBoundaryArc (intPairBasis B u v hdet) 0 ε ⊆ S)
    (z : EuclideanSpace ℝ (Fin 2)) (T η : ℝ)
    (hdiam : Metric.diam (normalsOn C S) ≤ T)
    (hnear : ∃ y ∈ normalsOn C S, dist y z ≤ η) :
    dist (normalizedEuclideanCovector C (selectedSupportAt B u v)) z ≤ T + η := by
  exact dist_le_add_of_mem_closure_of_exists_near (normalsOn_isBounded C S)
    (selectedSupportAt_normal_mem_closure_normalsOn_of_local_arc_subset
      B C u v hdet S ε hε hsubset) T η hdiam hnear

/-- A nearby normal anywhere over `S` transfers to the endpoint support,
provided `S` contains the endpoint's local boundary wedge. -/
theorem trace_selectedSupportAt_normal_proximity_of_arc_subset
    (u v d : ℤ × ℤ) (hdet : intDet u v ≠ 0) (S : Set TracePlane)
    (ε M N c H η : ℝ) (hε : 0 < ε)
    (hsubset : slopeBoundaryArc (intPairBasis traceBasis u v hdet) 0 ε ⊆ S)
    (hdiam : Metric.diam (normalsOn traceBasis S) ≤ M * Real.exp (-c * H))
    (hnear : ∃ y ∈ normalsOn traceBasis S,
      dist y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * H)) :
    dist (normalizedEuclideanCovector traceBasis (selectedSupportAt traceBasis u v))
      (NormedSpace.normalize (euclideanIntDirection d)) ≤
      (M + N) * Real.exp (-c * H) := by
  apply (selectedSupportAt_normal_dist_le_add_of_local_arc_subset
    traceBasis traceBasis u v hdet S ε hε hsubset
    (NormedSpace.normalize (euclideanIntDirection d))
    (M * Real.exp (-c * H)) η hdiam hnear).trans
  calc
    M * Real.exp (-c * H) + η ≤
        M * Real.exp (-c * H) + N * Real.exp (-c * H) := add_le_add le_rfl hη
    _ = (M + N) * Real.exp (-c * H) := by ring

/-- The determinant upper bound follows from normals anywhere over the
larger actual set; it is not an input. -/
theorem trace_selectedSupportAt_det_upper_of_arc_subset
    (u v d : ℤ × ℤ) (hdet : intDet u v ≠ 0) (hd : d ≠ (0, 0))
    (S : Set TracePlane) (ε M N c H η : ℝ) (hε : 0 < ε)
    (hsubset : slopeBoundaryArc (intPairBasis traceBasis u v hdet) 0 ε ⊆ S)
    (hdiam : Metric.diam (normalsOn traceBasis S) ≤ M * Real.exp (-c * H))
    (hnear : ∃ y ∈ normalsOn traceBasis S,
      dist y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * H)) :
    |integralCovectorDet
      (dualCoordinates traceBasis (selectedSupportAt traceBasis u v)) d| ≤
      traceNormalArcDetConstant M N * intEuclidean d * Real.exp (-c * H) := by
  have hproximity := trace_selectedSupportAt_normal_proximity_of_arc_subset
    u v d hdet S ε M N c H η hε hsubset hdiam hnear hη
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

/-- The conditional endpoint-height estimate using the normal diameter
and nearby normal of a larger actual set containing a local endpoint arc. -/
theorem trace_unresolved_direction_height_of_normal_arc_subset
    (u v d : ℤ × ℤ) (S : Set TracePlane) (A ε M N c H η : ℝ)
    (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hdet : |intDet u v| = 1)
    (hd : d ≠ (0, 0)) (hε : 0 < ε) (hc : 0 < c)
    (hsubset : slopeBoundaryArc
      (intPairBasis traceBasis u v (intDet_ne_zero_of_abs_eq_one hdet)) 0 ε ⊆ S)
    (hdiam : Metric.diam (normalsOn traceBasis S) ≤ M * Real.exp (-c * H))
    (hnear : ∃ y ∈ normalsOn traceBasis S,
      dist y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * H)) :
    0 < (traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c ∧
      H ≤ ((traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c) *
        intEuclidean d * A ^ 2 := by
  exact trace_unresolved_direction_height u v d A (traceNormalArcDetConstant M N) c H
    hA hu hdet hd (one_le_traceNormalArcDetConstant M N) hc
    (trace_selectedSupportAt_det_upper_of_arc_subset u v d
      (intDet_ne_zero_of_abs_eq_one hdet) hd S ε M N c H η hε hsubset hdiam hnear hη)

/-- The conditional unresolved arc scale for a larger actual normal set,
with the geometric arc comparison still explicit. -/
theorem trace_unresolved_direction_arc_bound_of_normal_arc_subset
    (u v d : ℤ × ℤ) (S : Set TracePlane) (A ε M N c H η C s : ℝ)
    (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hdet : |intDet u v| = 1)
    (hd : d ≠ (0, 0)) (hε : 0 < ε) (hc : 0 < c)
    (hH : 0 < H) (hC : 0 ≤ C) (hs0 : 0 ≤ s)
    (hsubset : slopeBoundaryArc
      (intPairBasis traceBasis u v (intDet_ne_zero_of_abs_eq_one hdet)) 0 ε ⊆ S)
    (hdiam : Metric.diam (normalsOn traceBasis S) ≤ M * Real.exp (-c * H))
    (hnear : ∃ y ∈ normalsOn traceBasis S,
      dist y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * H)) (hs : s ≤ C / (H * A)) :
    s ≤ C * Real.sqrt
        ((traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c) *
      Real.sqrt (intEuclidean d) / (H * Real.sqrt H) := by
  exact trace_unresolved_direction_arc_bound u v d A (traceNormalArcDetConstant M N)
    c H C s hA hu hdet hd (one_le_traceNormalArcDetConstant M N) hc hH hC hs0
    (trace_selectedSupportAt_det_upper_of_arc_subset u v d
      (intDet_ne_zero_of_abs_eq_one hdet) hd S ε M N c H η hε hsubset hdiam hnear hη) hs

end Markov
