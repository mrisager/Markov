import Markov.CanonicalCutoffAngleDecay
import Markov.NormalClosureProximity
import Markov.NormalArcTransfer
import Markov.BoundaryWedgeInclusion

/-! Endpoint-height control from an explicit angular witness in the closure
of an actual canonical cutoff normal set. Its exponential diameter decay
is proved; the proximity witness and its error bound remain hypotheses.
No attained witness in the open normal set or full Lemma 6 is asserted. -/

noncomputable section
open Set

namespace Markov

/-- A closure angular witness controls the actual selected endpoint normal
at exactly the given radius, including witnesses attained only at a limit. -/
theorem trace_cutoff_selectedSupport_normal_proximity_of_angle_near_closure
    (n : ℕ) (u v d : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v)
    (hd : d ≠ (0, 0)) (M N c η : ℝ)
    (hdiam : Metric.diam (normalsOn traceBasis (traceCutoffArc u v)) ≤
      M * Real.exp (-c * (n : ℝ)))
    (hnear : ∃ y ∈ closure (normalsOn traceBasis (traceCutoffArc u v)),
      InnerProductGeometry.angle y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * (n : ℝ))) :
    dist (normalizedEuclideanCovector traceBasis (selectedSupportAt traceBasis u v))
      (NormedSpace.normalize (euclideanIntDirection d)) ≤
        (M + N) * Real.exp (-c * (n : ℝ)) := by
  have hclosure : normalizedEuclideanCovector traceBasis
      (selectedSupportAt traceBasis u v) ∈
      closure (normalsOn traceBasis (traceCutoffArc u v)) :=
    consecutiveCutoffSlopes_selectedSupport_normal_mem_closure traceBasis traceBasis n u v h
  have hprox := normal_dist_le_add_of_mem_closure_of_exists_angle_near_closure
    traceBasis (traceCutoffArc u v) (fun _ hx => hx.1)
    (normalizedEuclideanCovector traceBasis (selectedSupportAt traceBasis u v))
    (NormedSpace.normalize (euclideanIntDirection d)) hclosure
    (NormedSpace.norm_normalize (euclideanIntDirection_ne_zero d hd))
    (M * Real.exp (-c * (n : ℝ))) η hdiam hnear
  apply hprox.trans
  calc
    M * Real.exp (-c * (n : ℝ)) + η ≤
        M * Real.exp (-c * (n : ℝ)) + N * Real.exp (-c * (n : ℝ)) :=
      add_le_add le_rfl hη
    _ = _ := by ring

/-- The arithmetic determinant upper estimate is a consequence of the
displayed closure witness and diameter estimate, rather than an input. -/
theorem trace_cutoff_selectedSupport_det_upper_of_angle_near_closure
    (n : ℕ) (u v d : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v)
    (hd : d ≠ (0, 0)) (M N c η : ℝ)
    (hdiam : Metric.diam (normalsOn traceBasis (traceCutoffArc u v)) ≤
      M * Real.exp (-c * (n : ℝ)))
    (hnear : ∃ y ∈ closure (normalsOn traceBasis (traceCutoffArc u v)),
      InnerProductGeometry.angle y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * (n : ℝ))) :
    |integralCovectorDet
      (dualCoordinates traceBasis (selectedSupportAt traceBasis u v)) d| ≤
      traceNormalArcDetConstant M N * intEuclidean d * Real.exp (-c * (n : ℝ)) := by
  have hdet : intDet u v ≠ 0 := by
    rw [(consecutiveCutoffSlopes_det_and_denominator_sum n u v h).1]
    norm_num
  have hprox := trace_cutoff_selectedSupport_normal_proximity_of_angle_near_closure
    n u v d h hd M N c η hdiam hnear hη
  have hupper := selectedSupportAt_det_upper_of_normal_proximity traceBasis
    u v d hdet hd (M + N) c (n : ℝ) hprox
  rw [norm_traceBasis_zero, norm_traceBasis_one] at hupper
  apply hupper.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_right _ (intEuclidean_nonneg d)
  calc
    (traceAxisLength + traceAxisLength) * (M + N) =
        (2 * traceAxisLength) * (M + N) := by ring
    _ ≤ traceNormalArcDetConstant M N := le_max_right _ _

/-- Uniform proved cutoff diameter decay supplies endpoint-height control
conditional only on the explicit closure angular witness and its error.
The logarithmic constant retains its exact dependence on that error. -/
theorem trace_cutoff_angle_near_closure_height_bound :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (u v d : ℤ × ℤ), ConsecutiveCutoffSlopes n u v → d ≠ (0, 0) →
      ∀ (A N η : ℝ), 1 ≤ A → intHeight u ≤ A →
      (∃ y ∈ closure (normalsOn traceBasis (traceCutoffArc u v)),
        InnerProductGeometry.angle y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η) →
      η ≤ N * Real.exp (-c * (n : ℝ)) →
      0 < (traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c ∧
        (n : ℝ) ≤
          ((traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c) *
            intEuclidean d * A ^ 2 := by
  obtain ⟨M, c, hM, hc, hdiam⟩ := trace_cutoff_normal_diam_decay
  refine ⟨M, c, hM, hc, ?_⟩
  intro n hn u v d h hd A N η hA hu hnear hη
  have hdet : |intDet u v| = 1 := by
    rw [(consecutiveCutoffSlopes_det_and_denominator_sum n u v h).1]
    norm_num
  exact trace_unresolved_direction_height u v d A (traceNormalArcDetConstant M N)
    c (n : ℝ) hA hu hdet hd (one_le_traceNormalArcDetConstant M N) hc
    (trace_cutoff_selectedSupport_det_upper_of_angle_near_closure
      n u v d h hd M N c η (hdiam n hn u v h) hnear hη)

end Markov
