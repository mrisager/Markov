import Markov.AngularNormals
import Markov.CutoffNormalEstimates

/-! Angular hypotheses on the actual canonical cutoff normal sets imply
the Euclidean inputs of `CutoffNormalEstimates`. Circle-arc containment,
angular width decay, and an actual nearby normal measured by angle remain
explicit assumptions. No exponential normal-turn tail or full Lemma 6 is
asserted here. -/

noncomputable section
open Set

namespace Markov

/-- Actual support normals of a canonical cutoff arc have unit Euclidean
norm, because the arc is part of the actual unit boundary. -/
theorem norm_eq_one_of_mem_trace_cutoff_normals (u v : ℤ × ℤ)
    (y : EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ normalsOn traceBasis (traceCutoffArc u v)) : ‖y‖ = 1 := by
  exact norm_eq_one_of_mem_normalsOn traceBasis (traceCutoffArc u v)
    (fun _ hx => hx.1) y hy

/-- Angular containment and angular-width decay give the Euclidean
diameter estimate for the actual normal set. -/
theorem trace_cutoff_normal_diam_le_of_angular_width
    (n : ℕ) (u v : ℤ × ℤ) (a b M c : ℝ) (hab : a ≤ b)
    (harc : normalsOn traceBasis (traceCutoffArc u v) ⊆ circleNormal '' Icc a b)
    (hwidth : b - a ≤ M * Real.exp (-c * (n : ℝ))) :
    Metric.diam (normalsOn traceBasis (traceCutoffArc u v)) ≤
      M * Real.exp (-c * (n : ℝ)) := by
  exact (normalsOn_diam_le_angular_width traceBasis (traceCutoffArc u v)
    a b hab harc).trans hwidth

/-- A nearby actual normal measured by the undirected Euclidean angle
provides the Euclidean distance witness used in endpoint transfer. -/
theorem trace_cutoff_normal_near_of_angle_near
    (u v d : ℤ × ℤ) (hd : d ≠ (0, 0)) (η : ℝ)
    (hnear : ∃ y ∈ normalsOn traceBasis (traceCutoffArc u v),
      InnerProductGeometry.angle y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η) :
    ∃ y ∈ normalsOn traceBasis (traceCutoffArc u v),
      dist y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η := by
  obtain ⟨y, hy, hyangle⟩ := hnear
  refine ⟨y, hy, ?_⟩
  exact (dist_le_angle_of_norm_eq_one y _
    (norm_eq_one_of_mem_trace_cutoff_normals u v y hy)
    (NormedSpace.norm_normalize (euclideanIntDirection_ne_zero d hd))).trans hyangle

/-- Angular width and angular proximity on the actual consecutive cutoff
gap control its selected endpoint normal. -/
theorem trace_cutoff_selectedSupport_normal_proximity_of_angular_bounds
    (n : ℕ) (u v d : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v)
    (hd : d ≠ (0, 0)) (a b M N c η : ℝ) (hab : a ≤ b)
    (harc : normalsOn traceBasis (traceCutoffArc u v) ⊆ circleNormal '' Icc a b)
    (hwidth : b - a ≤ M * Real.exp (-c * (n : ℝ)))
    (hnear : ∃ y ∈ normalsOn traceBasis (traceCutoffArc u v),
      InnerProductGeometry.angle y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * (n : ℝ))) :
    dist (normalizedEuclideanCovector traceBasis (selectedSupportAt traceBasis u v))
      (NormedSpace.normalize (euclideanIntDirection d)) ≤
      (M + N) * Real.exp (-c * (n : ℝ)) := by
  exact trace_cutoff_selectedSupport_normal_proximity n u v d h M N c η
    (trace_cutoff_normal_diam_le_of_angular_width n u v a b M c hab harc hwidth)
    (trace_cutoff_normal_near_of_angle_near u v d hd η hnear) hη

/-- The selected endpoint determinant upper bound follows from angular
hypotheses on the actual cutoff gap; no determinant bound is assumed. -/
theorem trace_cutoff_selectedSupport_det_upper_of_angular_bounds
    (n : ℕ) (u v d : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v)
    (hd : d ≠ (0, 0)) (a b M N c η : ℝ) (hab : a ≤ b)
    (harc : normalsOn traceBasis (traceCutoffArc u v) ⊆ circleNormal '' Icc a b)
    (hwidth : b - a ≤ M * Real.exp (-c * (n : ℝ)))
    (hnear : ∃ y ∈ normalsOn traceBasis (traceCutoffArc u v),
      InnerProductGeometry.angle y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * (n : ℝ))) :
    |integralCovectorDet
      (dualCoordinates traceBasis (selectedSupportAt traceBasis u v)) d| ≤
      traceNormalArcDetConstant M N * intEuclidean d * Real.exp (-c * (n : ℝ)) := by
  exact trace_cutoff_selectedSupport_det_upper n u v d h hd M N c η
    (trace_cutoff_normal_diam_le_of_angular_width n u v a b M c hab harc hwidth)
    (trace_cutoff_normal_near_of_angle_near u v d hd η hnear) hη

/-- Conditional endpoint-height control on an actual consecutive cutoff
gap from explicit angular containment, width decay, and angular proximity.
The Euclidean diameter and distance estimates are proved above. -/
theorem trace_unresolved_direction_height_of_cutoff_angular_bounds
    (n : ℕ) (u v d : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v)
    (A a b M N c η : ℝ) (hA : 1 ≤ A) (hu : intHeight u ≤ A)
    (hd : d ≠ (0, 0)) (hc : 0 < c) (hab : a ≤ b)
    (harc : normalsOn traceBasis (traceCutoffArc u v) ⊆ circleNormal '' Icc a b)
    (hwidth : b - a ≤ M * Real.exp (-c * (n : ℝ)))
    (hnear : ∃ y ∈ normalsOn traceBasis (traceCutoffArc u v),
      InnerProductGeometry.angle y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η)
    (hη : η ≤ N * Real.exp (-c * (n : ℝ))) :
    0 < (traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c ∧
      (n : ℝ) ≤
        ((traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c) *
          intEuclidean d * A ^ 2 := by
  exact trace_unresolved_direction_height_of_cutoff_normals
    n u v d h A M N c η hA hu hd hc
    (trace_cutoff_normal_diam_le_of_angular_width n u v a b M c hab harc hwidth)
    (trace_cutoff_normal_near_of_angle_near u v d hd η hnear) hη

end Markov
