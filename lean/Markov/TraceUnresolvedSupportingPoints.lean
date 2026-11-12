import Markov.TraceSupportLocation
import Markov.TraceCutoffNormalSeparation

/-! Genuine supporting points for an unresolved unit normal. The two
angularly displaced normals support points in the closure of the same
actual uncut component. Their Euclidean distance is bounded by the
variation of that component's signed radial parametrization. -/

noncomputable section
open Set
namespace Markov

/-- The incoming-angle convention records the actual corner atom at
every point of one traversal, including the initial point at the seam. -/
theorem traceBoundaryTurn_singleton_toReal_eq_incoming_jump
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) :
    (traceBoundaryTurn {traceBoundaryPath t}).toReal =
      traceCyclicAngleLift t - traceBoundaryIncomingAngle t := by
  by_cases ht0 : t = 0
  · subst t
    have hjump := traceBoundaryTurn_singleton_toReal_eq_jump 4 (by norm_num)
    rw [traceBoundaryPath_four_eq_zero] at hjump
    simp only [traceBoundaryIncomingAngle, ↓reduceIte]
    linarith [traceCyclicAngleLift_period_increment]
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    simpa only [traceBoundaryIncomingAngle, if_neg ht0] using
      traceBoundaryTurn_singleton_toReal_eq_jump t ⟨htpos, ht.2⟩

/-- Under the basic angular inequality, both displaced normals of an
unresolved normal support actual points in the closure of its component.
No uniqueness of a supporting point is required. -/
theorem trace_unresolved_component_supporting_points
    (H ε η : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength * H)))
    (z : EuclideanSpace ℝ (Fin 2)) (x : TracePlane)
    (hx : x ∈ traceUncutBoundary H)
    (hz : z ∈ closedAngularNeighborhood
      (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η) :
    ∃ (α : ℝ) (xMinus xPlus : TracePlane), z = circleNormal α ∧
      xMinus ∈ closure (connectedComponentIn (traceUncutBoundary H) x) ∧
      xPlus ∈ closure (connectedComponentIn (traceUncutBoundary H) x) ∧
      circleNormal (α - η) ∈ normalsOn traceBasis {xMinus} ∧
      circleNormal (α + η) ∈ normalsOn traceBasis {xPlus} := by
  obtain ⟨a, b, ha, hab, hb, hacut, hbcut, hcomp, hclosed⟩ :=
    traceUncutBoundary_exists_closed_path_component H hH x hx
  have hangle := hz
  rw [hcomp] at hangle
  obtain ⟨α, hα, hzeq⟩ :=
    exists_mem_Icc_eq_circleNormal_of_mem_closedAngularNeighborhood_of_subset
      (normalsOn traceBasis (traceBoundaryOpenArc a b))
      (traceBoundaryOpenArc_normals_isConnected a b ha hab hb).1
      (traceCyclicAngleLift a) (Function.leftLim traceCyclicAngleLift b) η
      (traceBoundaryOpenArc_normals_subset_lift_arc a b ha hb) z hangle
  have hajump := trace_real_cutoff_corner_atom_lower H (traceBoundaryPath a) hacut
  have hbjump := trace_real_cutoff_corner_atom_lower H (traceBoundaryPath b) hbcut
  rw [traceBoundaryTurn_singleton_toReal_eq_incoming_jump a ⟨ha, hab.le.trans hb⟩]
    at hajump
  rw [traceBoundaryTurn_singleton_toReal_eq_jump b ⟨ha.trans_lt hab, hb⟩] at hbjump
  have hεη : 0 < ε * η := mul_pos hε hη
  have hlower : traceBoundaryIncomingAngle a ≤ α - η := by
    nlinarith [hα.1]
  have hupper : α + η ≤ traceCyclicAngleLift b := by
    nlinarith [hα.2]
  have hminus : α - η ∈
      Icc (traceBoundaryIncomingAngle a) (traceCyclicAngleLift b) :=
    ⟨hlower, by linarith⟩
  have hplus : α + η ∈
      Icc (traceBoundaryIncomingAngle a) (traceCyclicAngleLift b) :=
    ⟨by linarith, hupper⟩
  obtain ⟨tMinus, htMinus, hnMinus⟩ := traceBoundary_closedArc_support_exists
    a b (α - η) ha hab hb hminus
  obtain ⟨tPlus, htPlus, hnPlus⟩ := traceBoundary_closedArc_support_exists
    a b (α + η) ha hab hb hplus
  refine ⟨α, traceBoundaryPath tMinus, traceBoundaryPath tPlus, hzeq,
    ?_, ?_, hnMinus, hnPlus⟩
  · rw [hclosed]
    exact ⟨tMinus, htMinus, rfl⟩
  · rw [hclosed]
    exact ⟨tPlus, htPlus, rfl⟩

/-- The same component has signed consecutive-cutoff labels, and the
distance between its two supporting points is at most its actual
Euclidean variation in the fixed original coordinates. -/
theorem trace_unresolved_actual_component_supporting_points
    (H ε η : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength * H)))
    (z : EuclideanSpace ℝ (Fin 2)) (x : TracePlane)
    (hx : x ∈ traceUncutBoundary H)
    (hz : z ∈ closedAngularNeighborhood
      (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η) :
    ∃ (k : Fin 8) (u v : ℤ × ℤ) (α : ℝ) (xMinus xPlus : TracePlane),
      ConsecutiveCutoffSlopes ⌊H⌋₊ u v ∧
      connectedComponentIn (traceUncutBoundary H) x =
        slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) ∧
      z = circleNormal α ∧
      xMinus ∈ closure (connectedComponentIn (traceUncutBoundary H) x) ∧
      xPlus ∈ closure (connectedComponentIn (traceUncutBoundary H) x) ∧
      circleNormal (α - η) ∈ normalsOn traceBasis {xMinus} ∧
      circleNormal (α + η) ∈ normalsOn traceBasis {xPlus} ∧
      dist (traceEuclideanCoordinates xMinus) (traceEuclideanCoordinates xPlus) ≤
        (signedTraceCutoffArcLength k u v).toReal := by
  obtain ⟨α, xMinus, xPlus, hzeq, hMinus, hPlus, hnMinus, hnPlus⟩ :=
    trace_unresolved_component_supporting_points H ε η hH hε hη hbasic z x hx hz
  obtain ⟨k, u, v, hcut, _, hcomp⟩ :=
    traceUncutBoundary_exists_signed_cutoff_component H hH x hx
  refine ⟨k, u, v, α, xMinus, xPlus, hcut, hcomp, hzeq,
    hMinus, hPlus, hnMinus, hnPlus, ?_⟩
  rw [hcomp] at hMinus hPlus
  exact dist_traceEuclideanCoordinates_le_signedTraceCutoffArcLength
    ⌊H⌋₊ k u v hcut xMinus xPlus hMinus hPlus

/-- Every actual unresolved unit normal has supporting points at both
offset angles in one actual component closure, with their distance
bounded by that same component's Euclidean variation. -/
theorem IsTraceUnresolvedNormal.supporting_points
    {z : EuclideanSpace ℝ (Fin 2)} {H η : ℝ}
    (hz : IsTraceUnresolvedNormal z H η) (ε : ℝ)
    (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength * H))) :
    ∃ x ∈ traceUncutBoundary H,
      ∃ (k : Fin 8) (u v : ℤ × ℤ) (α : ℝ) (xMinus xPlus : TracePlane),
      ConsecutiveCutoffSlopes ⌊H⌋₊ u v ∧
      connectedComponentIn (traceUncutBoundary H) x =
        slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) ∧
      z = circleNormal α ∧
      xMinus ∈ closure (connectedComponentIn (traceUncutBoundary H) x) ∧
      xPlus ∈ closure (connectedComponentIn (traceUncutBoundary H) x) ∧
      circleNormal (α - η) ∈ normalsOn traceBasis {xMinus} ∧
      circleNormal (α + η) ∈ normalsOn traceBasis {xPlus} ∧
      dist (traceEuclideanCoordinates xMinus) (traceEuclideanCoordinates xPlus) ≤
        (signedTraceCutoffArcLength k u v).toReal := by
  obtain ⟨x, hx, hmem⟩ := hz
  exact ⟨x, hx, trace_unresolved_actual_component_supporting_points
    H ε η hH hε hη hbasic z x hx hmem⟩

end Markov
