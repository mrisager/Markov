import Markov.TraceUnresolvedAssociation
import Markov.RealCutoffUnresolvedSizes

/-! Quantitative size estimates for actual unresolved trace-boundary
components. The real-cutoff component association, original integral
coordinates and the paper's basic angular-error assumption are used
directly. These bounds hold for every associated component; uniqueness of
the association and identification with geometric B_X are separate. -/

noncomputable section
open Set
namespace Markov

/-- Every actual component whose normal neighborhood contains a nonzero
integral direction has the real-height and square-root variation estimates.
The signed labels are a proved description of that same component. -/
theorem trace_unresolved_actual_component_sizes :
    ∃ Ch Ca : ℝ, 0 < Ch ∧ 0 < Ca ∧
      ∀ (H ε η : ℝ), 1 ≤ H → 0 < ε →
      (2 + ε) * η ≤ traceCornerLowerConstant *
        Real.exp (-(2 * traceAxisLength) * H) →
      ∀ (d : ℤ × ℤ), d ≠ (0, 0) →
      ∀ x ∈ traceUncutBoundary H,
      NormedSpace.normalize (euclideanIntDirection d) ∈
        closedAngularNeighborhood
          (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η →
      ∃ (k : Fin 8) (u v : ℤ × ℤ),
        ConsecutiveCutoffSlopes ⌊H⌋₊ u v ∧
        connectedComponentIn (traceUncutBoundary H) x =
          slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) ∧
        H ≤ Ch * intEuclidean d *
          (min (intHeight (inverseSignedSectorCoordinates k u))
            (intHeight (inverseSignedSectorCoordinates k v))) ^ 2 ∧
        (signedTraceCutoffArcLength k u v).toReal ≤
          Ca * Real.sqrt (intEuclidean d) / (H * Real.sqrt H) := by
  obtain ⟨Ch, Ca, hCh, hCa, hsize⟩ :=
    real_cutoff_signed_unresolved_height_and_arc_bound
  refine ⟨Ch, Ca, hCh, hCa, ?_⟩
  intro H ε η hH hε hbasic d hd x hx hmem
  obtain ⟨k, u, v, h, _, hcomp⟩ :=
    traceUncutBoundary_exists_signed_cutoff_component H hH x hx
  rw [hcomp] at hmem
  exact ⟨k, u, v, h, hcomp, hsize H ε η hH hε hbasic k u v d h hd hmem⟩

/-- The paper-shaped unresolved predicate has an actual component
witness satisfying both quantitative conclusions, uniformly in K,H,η.
The Euclidean arc size is the actual radial curve variation. -/
theorem trace_unresolved_direction_sizes :
    ∃ Ch Ca : ℝ, 0 < Ch ∧ 0 < Ca ∧
      ∀ (K H ε η : ℝ), 1 ≤ H → 0 < ε →
      (2 + ε) * η ≤ traceCornerLowerConstant *
        Real.exp (-(2 * traceAxisLength) * H) →
      ∀ (d : ℤ × ℤ), IsTraceUnresolved d K H η →
      ∃ x ∈ traceUncutBoundary H, ∃ (k : Fin 8) (u v : ℤ × ℤ),
        ConsecutiveCutoffSlopes ⌊H⌋₊ u v ∧
        connectedComponentIn (traceUncutBoundary H) x =
          slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) ∧
        H ≤ Ch * intEuclidean d *
          (min (intHeight (inverseSignedSectorCoordinates k u))
            (intHeight (inverseSignedSectorCoordinates k v))) ^ 2 ∧
        (signedTraceCutoffArcLength k u v).toReal ≤
          Ca * Real.sqrt (intEuclidean d) / (H * Real.sqrt H) := by
  obtain ⟨Ch, Ca, hCh, hCa, hsize⟩ := trace_unresolved_actual_component_sizes
  refine ⟨Ch, Ca, hCh, hCa, ?_⟩
  intro K H ε η hH hε hbasic d hUnresolved
  obtain ⟨hd, _, x, hx, hmem⟩ := hUnresolved
  exact ⟨x, hx, hsize H ε η hH hε hbasic d hd x hx hmem⟩

end Markov
