import Markov.BoundaryArcComponents
import Markov.SignedTraceArcs

/-! Cutoff components in the eight signed coordinate sectors.
Changing basis preserves the norm and the full primitive cutoff set.
These local statements use consecutive cutoff slopes in the chosen sector. -/

noncomputable section
namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Consecutive cutoff endpoints in any signed sector identify the
maximal connected component of the original actual boundary difference.
No symmetry of the source norm under the signed coordinate map is used. -/
theorem transformedCutoffSlopes_connectedComponentIn_eq_arc
    (B : Module.Basis (Fin 2) ℝ E) (k : Fin 8) (H : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H (signedSectorCoordinates k u)
      (signedSectorCoordinates k v)) (t : ℝ)
    (ht : t ∈ Set.Ioo (cutoffSlope (signedSectorCoordinates k u))
      (cutoffSlope (signedSectorCoordinates k v))) :
    connectedComponentIn
      (frontier (Metric.closedBall (0 : E) 1) \ (↑(cutoffCorners B H) : Set E))
      (radialBasisSection (signedSectorBasis B k) t) =
        slopeBoundaryArc (signedSectorBasis B k)
          (cutoffSlope (signedSectorCoordinates k u))
          (cutoffSlope (signedSectorCoordinates k v)) := by
  rw [← cutoffCorners_signedSectorBasis B k H]
  exact consecutiveCutoffSlopes_connectedComponentIn_eq_arc
    (signedSectorBasis B k) H (signedSectorCoordinates k u) (signedSectorCoordinates k v)
    h t ht

end Markov
