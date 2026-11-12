import Markov.BoundaryWedgeInclusion
import Markov.NormalArcTransfer

/-! Conditional normal estimates on actual consecutive canonical cutoff arcs.
The endpoint wedge inclusion and determinant-one property follow from
actual cutoff consecutiveness. The diameter of the whole actual normal
arc, a nearby actual normal anywhere over that arc, and its small error
remain explicit. No exponential normal-turn tail or full Lemma 6 is
asserted here. -/

noncomputable section
namespace Markov

private theorem trace_cutoff_local_arc_subset
    (n : ℕ) (u v : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v)
    (hd : intDet u v ≠ 0) :
    slopeBoundaryArc (intPairBasis traceBasis u v hd) 0 1 ⊆ traceCutoffArc u v := by
  exact intPairBasis_local_arc_subset_slopeBoundaryArc traceBasis u v hd
    ((mem_cutoffSlopesUpTo n u).mp h.1).1
    ((mem_cutoffSlopesUpTo n v).mp h.2.1).1 h.2.2.1 1

/-- The actual cutoff membership gives the integral height bound on both
endpoints without a separate arithmetic height assumption. -/
theorem consecutiveCutoffSlopes_intHeight_le (n : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes n u v) :
    intHeight u ≤ (n : ℝ) ∧ intHeight v ≤ (n : ℝ) := by
  exact ⟨((mem_primitiveDirectionsUpTo n u).mp
      (cutoffSlope_mem_primitiveDirectionsUpTo n u h.1)).2,
    ((mem_primitiveDirectionsUpTo n v).mp
      (cutoffSlope_mem_primitiveDirectionsUpTo n v h.2.1)).2⟩

/-- A nearby actual normal anywhere on a consecutive cutoff gap controls
the selected endpoint normal of that gap. -/
theorem trace_cutoff_selectedSupport_normal_proximity
    (n : ℕ) (u v d : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v)
    (M N c η : ℝ)
    (hdiam : Metric.diam (normalsOn traceBasis (traceCutoffArc u v)) ≤
      M * Real.exp (-c * (n : ℝ)))
    (hnear : ∃ y ∈ normalsOn traceBasis (traceCutoffArc u v),
      dist y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * (n : ℝ))) :
    dist (normalizedEuclideanCovector traceBasis (selectedSupportAt traceBasis u v))
      (NormedSpace.normalize (euclideanIntDirection d)) ≤
      (M + N) * Real.exp (-c * (n : ℝ)) := by
  have hd : intDet u v ≠ 0 :=
    intDet_ne_zero_of_abs_eq_one (consecutiveCutoffSlopes_abs_det n u v h)
  exact trace_selectedSupportAt_normal_proximity_of_arc_subset
    u v d hd (traceCutoffArc u v) 1 M N c n η (by norm_num)
    (trace_cutoff_local_arc_subset n u v h hd) hdiam hnear hη

/-- The determinant upper bound is derived on the actual cutoff gap,
using the same natural-number cutoff in the exponential decay. -/
theorem trace_cutoff_selectedSupport_det_upper
    (n : ℕ) (u v d : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v)
    (hd : d ≠ (0, 0)) (M N c η : ℝ)
    (hdiam : Metric.diam (normalsOn traceBasis (traceCutoffArc u v)) ≤
      M * Real.exp (-c * (n : ℝ)))
    (hnear : ∃ y ∈ normalsOn traceBasis (traceCutoffArc u v),
      dist y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * (n : ℝ))) :
    |integralCovectorDet
      (dualCoordinates traceBasis (selectedSupportAt traceBasis u v)) d| ≤
      traceNormalArcDetConstant M N * intEuclidean d * Real.exp (-c * (n : ℝ)) := by
  have hdet : intDet u v ≠ 0 :=
    intDet_ne_zero_of_abs_eq_one (consecutiveCutoffSlopes_abs_det n u v h)
  exact trace_selectedSupportAt_det_upper_of_arc_subset
    u v d hdet hd (traceCutoffArc u v) 1 M N c n η (by norm_num)
    (trace_cutoff_local_arc_subset n u v h hdet) hdiam hnear hη

/-- The conditional endpoint-height estimate for an actual consecutive
cutoff gap. No determinant upper bound or local-arc inclusion is assumed;
the exponential diameter and nearby-normal estimates remain inputs. -/
theorem trace_unresolved_direction_height_of_cutoff_normals
    (n : ℕ) (u v d : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v)
    (A M N c η : ℝ) (hA : 1 ≤ A) (hu : intHeight u ≤ A)
    (hd : d ≠ (0, 0)) (hc : 0 < c)
    (hdiam : Metric.diam (normalsOn traceBasis (traceCutoffArc u v)) ≤
      M * Real.exp (-c * (n : ℝ)))
    (hnear : ∃ y ∈ normalsOn traceBasis (traceCutoffArc u v),
      dist y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * (n : ℝ))) :
    0 < (traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c ∧
      (n : ℝ) ≤
        ((traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c) *
          intEuclidean d * A ^ 2 := by
  have hdet : |intDet u v| = 1 := consecutiveCutoffSlopes_abs_det n u v h
  exact trace_unresolved_direction_height_of_normal_arc_subset
    u v d (traceCutoffArc u v) A 1 M N c n η hA hu hdet hd (by norm_num) hc
    (trace_cutoff_local_arc_subset n u v h (intDet_ne_zero_of_abs_eq_one hdet))
    hdiam hnear hη

end Markov
