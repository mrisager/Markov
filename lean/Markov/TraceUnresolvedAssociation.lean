import Markov.GlobalCutoffCoverage
import Markov.RealCutoffCorners
import Markov.ClosedAngularNeighborhood
import Markov.NormalDeterminant

/-! Unresolved directions are associated with actual connected components
of the trace unit boundary after the real primitive cutoff is removed.
The angular condition uses the closed infimal-distance neighborhood of the
actual normal set, with the stated radius retained exactly. At height at
least one these components are precisely the signed consecutive cutoff
arcs at the natural floor. The association is existential, without a
uniqueness assertion for signed-sector descriptions. -/

noncomputable section
open Set
namespace Markov

/-- The actual trace unit boundary after deleting every primitive corner
whose original integral height is at most the real cutoff `H`. -/
def traceUncutBoundary (H : ℝ) : Set TracePlane :=
  frontier (Metric.closedBall (0 : TracePlane) 1) \ realCutoffCorners traceBasis H

/-- A nonzero integral direction of Euclidean size at most `K` is
unresolved when it belongs to the closed angular neighborhood, defined by
infimal angular distance, of the actual normals on some uncut component. -/
def IsTraceUnresolved (d : ℤ × ℤ) (K H η : ℝ) : Prop :=
  d ≠ (0, 0) ∧ intEuclidean d ≤ K ∧
    ∃ x ∈ traceUncutBoundary H,
      NormedSpace.normalize (euclideanIntDirection d) ∈
        closedAngularNeighborhood
          (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η

/-- The real uncut boundary is exactly the old natural-cutoff boundary
difference at the natural floor; this is equality of actual sets. -/
theorem traceUncutBoundary_eq_natFloor (H : ℝ) (hH : 0 ≤ H) :
    traceUncutBoundary H =
      frontier (Metric.closedBall (0 : TracePlane) 1) \
        (↑(cutoffCorners traceBasis ⌊H⌋₊) : Set TracePlane) := by
  rw [traceUncutBoundary, realCutoffCorners_eq_natFloor traceBasis H hH]

/-- Every actual uncut boundary point has a signed consecutive-cutoff
description, including an exact identity for its connected component. -/
theorem traceUncutBoundary_exists_signed_cutoff_component
    (H : ℝ) (hH : 1 ≤ H) (x : TracePlane) (hx : x ∈ traceUncutBoundary H) :
    ∃ (k : Fin 8) (u v : ℤ × ℤ), ConsecutiveCutoffSlopes ⌊H⌋₊ u v ∧
      x ∈ slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) ∧
      connectedComponentIn (traceUncutBoundary H) x =
        slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) := by
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have hfloor : 1 ≤ ⌊H⌋₊ := (Nat.le_floor_iff hH0).mpr (by simpa using hH)
  rw [traceUncutBoundary_eq_natFloor H hH0] at hx ⊢
  exact uncut_boundary_exists_signed_cutoff_component traceBasis ⌊H⌋₊ hfloor x hx

/-- Conversely, the radial midpoint of every signed consecutive cutoff
arc is uncut, and its actual connected component is exactly that arc. -/
theorem signed_cutoff_component_exists_mem_traceUncutBoundary
    (H : ℝ) (hH : 1 ≤ H) (k : Fin 8) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes ⌊H⌋₊ u v) :
    ∃ x ∈ traceUncutBoundary H,
      x ∈ slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) ∧
      connectedComponentIn (traceUncutBoundary H) x =
        slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) := by
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have horder : cutoffSlope u < cutoffSlope v :=
    ((consecutiveCutoffSlopes_iff_slope ⌊H⌋₊ u v).mp h).2.2.1
  let t : ℝ := (cutoffSlope u + cutoffSlope v) / 2
  have ht : t ∈ Ioo (cutoffSlope u) (cutoffSlope v) := by
    dsimp [t]
    constructor <;> linarith
  have hxarc : radialBasisSection (signedSectorBasis traceBasis k) t ∈
      slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) := by
    rw [← radialBasisSection_image_Ioo]
    exact ⟨t, ht, rfl⟩
  have hx := consecutiveCutoffSlopes_arc_subset_boundary_difference
    (signedSectorBasis traceBasis k) ⌊H⌋₊ u v h hxarc
  rw [cutoffCorners_signedSectorBasis] at hx
  have hcomp := consecutiveCutoffSlopes_connectedComponentIn_eq_arc
    (signedSectorBasis traceBasis k) ⌊H⌋₊ u v h t ht
  rw [cutoffCorners_signedSectorBasis] at hcomp
  refine ⟨radialBasisSection (signedSectorBasis traceBasis k) t, ?_, hxarc, ?_⟩
  · rw [traceUncutBoundary_eq_natFloor H hH0]
    exact hx
  · rw [traceUncutBoundary_eq_natFloor H hH0]
    exact hcomp

/-- Actual unresolved-component membership is equivalent to membership
in the exact same closed angular neighborhood of a signed cutoff arc.
All integer directions and all normals retain their original coordinates. -/
theorem isTraceUnresolved_iff_exists_signed_cutoff_component
    (d : ℤ × ℤ) (K H η : ℝ) (hH : 1 ≤ H) :
    IsTraceUnresolved d K H η ↔
      d ≠ (0, 0) ∧ intEuclidean d ≤ K ∧
        ∃ (k : Fin 8) (u v : ℤ × ℤ), ConsecutiveCutoffSlopes ⌊H⌋₊ u v ∧
          NormedSpace.normalize (euclideanIntDirection d) ∈
            closedAngularNeighborhood (normalsOn traceBasis
              (slopeBoundaryArc (signedSectorBasis traceBasis k)
                (cutoffSlope u) (cutoffSlope v))) η := by
  constructor
  · rintro ⟨hd, hK, x, hx, hmem⟩
    obtain ⟨k, u, v, h, _, hcomp⟩ :=
      traceUncutBoundary_exists_signed_cutoff_component H hH x hx
    rw [hcomp] at hmem
    exact ⟨hd, hK, k, u, v, h, hmem⟩
  · rintro ⟨hd, hK, k, u, v, h, hmem⟩
    obtain ⟨x, hx, _, hcomp⟩ :=
      signed_cutoff_component_exists_mem_traceUncutBoundary H hH k u v h
    refine ⟨hd, hK, x, hx, ?_⟩
    rw [hcomp]
    exact hmem

/-- An unresolved direction has an actual component witness together
with its signed cutoff identity and the unchanged closed-neighborhood
condition on that arc. -/
theorem IsTraceUnresolved.exists_signed_cutoff_component
    {d : ℤ × ℤ} {K H η : ℝ} (h : IsTraceUnresolved d K H η) (hH : 1 ≤ H) :
    ∃ x ∈ traceUncutBoundary H, ∃ (k : Fin 8) (u v : ℤ × ℤ),
      ConsecutiveCutoffSlopes ⌊H⌋₊ u v ∧
      x ∈ slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) ∧
      connectedComponentIn (traceUncutBoundary H) x =
        slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) ∧
      NormedSpace.normalize (euclideanIntDirection d) ∈
        closedAngularNeighborhood (normalsOn traceBasis
          (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))) η := by
  obtain ⟨_, _, x, hx, hmem⟩ := h
  obtain ⟨k, u, v, hconsecutive, hxarc, hcomp⟩ :=
    traceUncutBoundary_exists_signed_cutoff_component H hH x hx
  rw [hcomp] at hmem
  exact ⟨x, hx, k, u, v, hconsecutive, hxarc, hcomp, hmem⟩

end Markov
