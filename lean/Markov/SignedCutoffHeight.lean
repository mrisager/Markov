import Markov.SignedCutoffEndpointClosure
import Markov.SignedCutoffArcEmbedding
import Markov.ClosedAngularNeighborhood
import Markov.NormalUnresolved

/-! Height control for the smaller original endpoint of an actual signed
cutoff component. Closed angular-neighborhood membership supplies an exact
closure witness. Both original inward selected supports are available, so
the smaller endpoint can be used without transforming the tested direction.
The exponential neighborhood error remains an explicit hypothesis. -/

noncomputable section
open Set
namespace Markov

/-- Closed-neighborhood membership gives a witness in the closure of the
actual normal set of the signed component, at the original radius. -/
theorem signed_cutoff_angular_neighborhood_witness
    (n : ℕ) (k : Fin 8) (u v d : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v)
    (η : ℝ)
    (hmem : NormedSpace.normalize (euclideanIntDirection d) ∈
      closedAngularNeighborhood (normalsOn traceBasis
        (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))) η) :
    ∃ y ∈ closure (normalsOn traceBasis
      (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))),
      InnerProductGeometry.angle y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η := by
  have hleft := signedConsecutiveCutoffSlopes_selectedSupport_normal_mem_closure
    traceBasis traceBasis n k u v h
  have hnonempty : (normalsOn traceBasis
      (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))).Nonempty :=
    closure_nonempty_iff.mp ⟨_, hleft⟩
  exact ((mem_closedAngularNeighborhood_iff_exists_mem_closure _ hnonempty
    (norm_eq_one_of_mem_normalsOn traceBasis _ (fun _ hx => hx.1)) _ η).mp hmem).2

/-- A selected endpoint in the actual normal closure has the determinant
upper bound supplied by the actual diameter and a closure-angle witness.
Every determinant and Euclidean direction uses the original trace basis. -/
theorem trace_selectedSupportAt_det_upper_of_angle_near_closure
    (u v d : ℤ × ℤ) (S : Set TracePlane) (hS : ∀ x ∈ S, ‖x‖ = 1)
    (hdet : intDet u v ≠ 0) (hd : d ≠ (0, 0)) (M N c H η : ℝ)
    (hclosure : normalizedEuclideanCovector traceBasis (selectedSupportAt traceBasis u v) ∈
      closure (normalsOn traceBasis S))
    (hdiam : Metric.diam (normalsOn traceBasis S) ≤ M * Real.exp (-c * H))
    (hnear : ∃ y ∈ closure (normalsOn traceBasis S),
      InnerProductGeometry.angle y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * H)) :
    |integralCovectorDet (dualCoordinates traceBasis (selectedSupportAt traceBasis u v)) d| ≤
      traceNormalArcDetConstant M N * intEuclidean d * Real.exp (-c * H) := by
  have hprox := normal_dist_le_add_of_mem_closure_of_exists_angle_near_closure
    traceBasis S hS
    (normalizedEuclideanCovector traceBasis (selectedSupportAt traceBasis u v))
    (NormedSpace.normalize (euclideanIntDirection d)) hclosure
    (NormedSpace.norm_normalize (euclideanIntDirection_ne_zero d hd))
    (M * Real.exp (-c * H)) η hdiam hnear
  have hproximity : dist
      (normalizedEuclideanCovector traceBasis (selectedSupportAt traceBasis u v))
      (NormedSpace.normalize (euclideanIntDirection d)) ≤ (M + N) * Real.exp (-c * H) := by
    apply hprox.trans
    calc
      M * Real.exp (-c * H) + η ≤
          M * Real.exp (-c * H) + N * Real.exp (-c * H) := add_le_add le_rfl hη
      _ = _ := by ring
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

/-- The smaller original endpoint gives height control at any positive
rate for which the displayed actual normal-diameter bound is available. -/
theorem signed_cutoff_closedAngularNeighborhood_height_of_diameter
    (n : ℕ) (k : Fin 8) (u v d : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v)
    (A M N c η : ℝ) (hA : 1 ≤ A)
    (hmin : min (intHeight (inverseSignedSectorCoordinates k u))
      (intHeight (inverseSignedSectorCoordinates k v)) ≤ A)
    (hd : d ≠ (0, 0)) (hc : 0 < c)
    (hdiam : Metric.diam (normalsOn traceBasis
      (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))) ≤
      M * Real.exp (-c * (n : ℝ)))
    (hmem : NormedSpace.normalize (euclideanIntDirection d) ∈
      closedAngularNeighborhood (normalsOn traceBasis
        (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))) η)
    (hη : η ≤ N * Real.exp (-c * (n : ℝ))) :
    0 < (traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c ∧
      (n : ℝ) ≤
        ((traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c) *
          intEuclidean d * A ^ 2 := by
  have hdetuv : intDet u v = 1 :=
    (consecutiveCutoffSlopes_det_and_denominator_sum n u v h).1
  have hdet : |intDet (inverseSignedSectorCoordinates k u)
      (inverseSignedSectorCoordinates k v)| = 1 := by
    rw [inverseSignedSectorCoordinates_det]
    split_ifs <;> simp only [hdetuv] <;> norm_num
  have hdetreverse : |intDet (inverseSignedSectorCoordinates k v)
      (inverseSignedSectorCoordinates k u)| = 1 := by
    have hswap : intDet (inverseSignedSectorCoordinates k v)
        (inverseSignedSectorCoordinates k u) =
        -intDet (inverseSignedSectorCoordinates k u) (inverseSignedSectorCoordinates k v) := by
      dsimp [intDet]
      ring
    rw [hswap, abs_neg, hdet]
  have hnear := signed_cutoff_angular_neighborhood_witness n k u v d h η hmem
  obtain ⟨hleft, hright⟩ :=
    signedConsecutiveCutoffSlopes_both_selectedSupport_normals_mem_closure n k u v h
  rcases min_le_iff.mp hmin with hu | hv
  · exact trace_unresolved_direction_height
      (inverseSignedSectorCoordinates k u) (inverseSignedSectorCoordinates k v) d
      A (traceNormalArcDetConstant M N) c (n : ℝ) hA hu hdet hd
      (one_le_traceNormalArcDetConstant M N) hc
      (trace_selectedSupportAt_det_upper_of_angle_near_closure
        _ _ d _ (fun _ hx => hx.1) (intDet_ne_zero_of_abs_eq_one hdet) hd
        M N c (n : ℝ) η hleft hdiam hnear hη)
  · exact trace_unresolved_direction_height
      (inverseSignedSectorCoordinates k v) (inverseSignedSectorCoordinates k u) d
      A (traceNormalArcDetConstant M N) c (n : ℝ) hA hv hdetreverse hd
      (one_le_traceNormalArcDetConstant M N) hc
      (trace_selectedSupportAt_det_upper_of_angle_near_closure
        _ _ d _ (fun _ hx => hx.1) (intDet_ne_zero_of_abs_eq_one hdetreverse) hd
        M N c (n : ℝ) η hright hdiam hnear hη)

/-- Uniform proved signed normal-diameter decay yields the smaller-endpoint
height estimate from actual closed angular-neighborhood membership. -/
theorem signed_cutoff_closedAngularNeighborhood_height_bound :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (k : Fin 8) (u v d : ℤ × ℤ), ConsecutiveCutoffSlopes n u v → d ≠ (0, 0) →
      ∀ (A N η : ℝ), 1 ≤ A →
      min (intHeight (inverseSignedSectorCoordinates k u))
        (intHeight (inverseSignedSectorCoordinates k v)) ≤ A →
      NormedSpace.normalize (euclideanIntDirection d) ∈
        closedAngularNeighborhood (normalsOn traceBasis
          (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))) η →
      η ≤ N * Real.exp (-c * (n : ℝ)) →
      0 < (traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c ∧
        (n : ℝ) ≤
          ((traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c) *
            intEuclidean d * A ^ 2 := by
  obtain ⟨M, c, hM, hc, hdiam⟩ := signed_cutoff_normal_diam_decay
  refine ⟨M, c, hM, hc, ?_⟩
  intro n hn k u v d h hd A N η hA hmin hmem hη
  exact signed_cutoff_closedAngularNeighborhood_height_of_diameter
    n k u v d h A M N c η hA hmin hd hc (hdiam n hn k u v h) hmem hη

end Markov
