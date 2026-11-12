import Markov.SupportAngleEnvelope
import Markov.AngularCutoffEstimates

/-! The support-angle envelope of a consecutive trace cutoff arc.
Endpoint order and containment of the arc's normal directions follow from
the construction. The endpoint estimates take envelope width and angular
proximity bounds as hypotheses. -/

noncomputable section
open Set

namespace Markov

/-- A consecutive cutoff gap contains a genuine radial unit-boundary
point at any strictly intermediate slope. -/
theorem traceCutoffArc_nonempty (n : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes n u v) : (traceCutoffArc u v).Nonempty := by
  have huv := ((consecutiveCutoffSlopes_iff_slope n u v).mp h).2.2.1
  obtain ⟨t, hut, htv⟩ := exists_between huv
  refine ⟨radialBasisSection traceBasis t, ?_⟩
  exact ⟨norm_radialBasisSection traceBasis t,
    radialBasisSection_coord_zero_pos traceBasis t,
    by simpa only [basisSlope_radialBasisSection] using hut,
    by simpa only [basisSlope_radialBasisSection] using htv⟩

/-- The actual envelope endpoints of a consecutive cutoff arc are ordered;
this fact follows from the nonempty arc. -/
theorem trace_cutoff_supportAngleLower_le_upper (n : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes n u v) :
    supportAngleLower traceBasis (traceCutoffArc u v) ≤
      supportAngleUpper traceBasis (traceCutoffArc u v) :=
  supportAngleLower_le_upper traceBasis (traceCutoffArc u v) (traceCutoffArc_nonempty n u v h)

/-- Every actual normal of the cutoff arc lies in the closed interval
envelope of its actual support angles. -/
theorem trace_cutoff_normals_subset_supportAngle_envelope (u v : ℤ × ℤ) :
    normalsOn traceBasis (traceCutoffArc u v) ⊆ circleNormal ''
      Icc (supportAngleLower traceBasis (traceCutoffArc u v))
        (supportAngleUpper traceBasis (traceCutoffArc u v)) :=
  normalsOn_subset_supportAngle_envelope traceBasis (traceCutoffArc u v) (fun _ hx => hx.1)

/-- The actual envelope width bounds the Euclidean diameter of the actual
cutoff normal set, with its angular containment proved above. -/
theorem trace_cutoff_normal_diam_le_supportAngle_width (n : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes n u v) :
    Metric.diam (normalsOn traceBasis (traceCutoffArc u v)) ≤
      supportAngleUpper traceBasis (traceCutoffArc u v) -
        supportAngleLower traceBasis (traceCutoffArc u v) :=
  normalsOn_diam_le_angular_width traceBasis (traceCutoffArc u v) _ _
    (trace_cutoff_supportAngleLower_le_upper n u v h)
    (trace_cutoff_normals_subset_supportAngle_envelope u v)

/-- Exponential decay of the actual angle-envelope width gives the
Euclidean normal-diameter input. The decay remains an explicit hypothesis. -/
theorem trace_cutoff_normal_diam_le_of_supportAngle_width
    (n : ℕ) (u v : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v) (M c : ℝ)
    (hwidth : supportAngleUpper traceBasis (traceCutoffArc u v) -
      supportAngleLower traceBasis (traceCutoffArc u v) ≤ M * Real.exp (-c * (n : ℝ))) :
    Metric.diam (normalsOn traceBasis (traceCutoffArc u v)) ≤
      M * Real.exp (-c * (n : ℝ)) :=
  (trace_cutoff_normal_diam_le_supportAngle_width n u v h).trans hwidth

/-- Width decay for the actual envelope and proximity of an actual normal
control the selected endpoint normal. -/
theorem trace_cutoff_selectedSupport_normal_proximity_of_supportAngle_width
    (n : ℕ) (u v d : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v)
    (hd : d ≠ (0, 0)) (M N c η : ℝ)
    (hwidth : supportAngleUpper traceBasis (traceCutoffArc u v) -
      supportAngleLower traceBasis (traceCutoffArc u v) ≤ M * Real.exp (-c * (n : ℝ)))
    (hnear : ∃ y ∈ normalsOn traceBasis (traceCutoffArc u v),
      InnerProductGeometry.angle y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * (n : ℝ))) :
    dist (normalizedEuclideanCovector traceBasis (selectedSupportAt traceBasis u v))
      (NormedSpace.normalize (euclideanIntDirection d)) ≤
      (M + N) * Real.exp (-c * (n : ℝ)) := by
  exact trace_cutoff_selectedSupport_normal_proximity_of_angular_bounds
    n u v d h hd _ _ M N c η
    (trace_cutoff_supportAngleLower_le_upper n u v h)
    (trace_cutoff_normals_subset_supportAngle_envelope u v) hwidth hnear hη

/-- The selected endpoint determinant upper bound follows from decay of
the actual angle-envelope width and an actual angular proximity witness. -/
theorem trace_cutoff_selectedSupport_det_upper_of_supportAngle_width
    (n : ℕ) (u v d : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v)
    (hd : d ≠ (0, 0)) (M N c η : ℝ)
    (hwidth : supportAngleUpper traceBasis (traceCutoffArc u v) -
      supportAngleLower traceBasis (traceCutoffArc u v) ≤ M * Real.exp (-c * (n : ℝ)))
    (hnear : ∃ y ∈ normalsOn traceBasis (traceCutoffArc u v),
      InnerProductGeometry.angle y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * (n : ℝ))) :
    |integralCovectorDet
      (dualCoordinates traceBasis (selectedSupportAt traceBasis u v)) d| ≤
      traceNormalArcDetConstant M N * intEuclidean d * Real.exp (-c * (n : ℝ)) := by
  exact trace_cutoff_selectedSupport_det_upper_of_angular_bounds
    n u v d h hd _ _ M N c η
    (trace_cutoff_supportAngleLower_le_upper n u v h)
    (trace_cutoff_normals_subset_supportAngle_envelope u v) hwidth hnear hη

/-- Conditional endpoint-height control using the actual support-angle
envelope. The angular containment and endpoint order are proved, while
width decay and proximity to the target direction remain explicit. -/
theorem trace_unresolved_direction_height_of_cutoff_supportAngle_width
    (n : ℕ) (u v d : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v)
    (A M N c η : ℝ) (hA : 1 ≤ A) (hu : intHeight u ≤ A)
    (hd : d ≠ (0, 0)) (hc : 0 < c)
    (hwidth : supportAngleUpper traceBasis (traceCutoffArc u v) -
      supportAngleLower traceBasis (traceCutoffArc u v) ≤ M * Real.exp (-c * (n : ℝ)))
    (hnear : ∃ y ∈ normalsOn traceBasis (traceCutoffArc u v),
      InnerProductGeometry.angle y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * (n : ℝ))) :
    0 < (traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c ∧
      (n : ℝ) ≤
        ((traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c) *
          intEuclidean d * A ^ 2 := by
  exact trace_unresolved_direction_height_of_cutoff_angular_bounds
    n u v d h A _ _ M N c η hA hu hd hc
    (trace_cutoff_supportAngleLower_le_upper n u v h)
    (trace_cutoff_normals_subset_supportAngle_envelope u v) hwidth hnear hη

end Markov
