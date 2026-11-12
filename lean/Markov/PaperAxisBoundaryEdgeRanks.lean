import Markov.PaperAxisBoundaryRanks
import Mathlib.Data.Fin.Rev

/-! Literal actual EDGE gluing in the chosen clockwise boundary ranks.
The old marked-coordinate rank preservation becomes boundary-rank reversal. -/
noncomputable section
open Set
namespace Markov

/-- Actual quotient EDGE gluing reverses the chosen clockwise boundary rank
on the opposite side, with its exact cardinality cast displayed. -/
theorem paperAxisProperEndpointBoundarySortedTag_edgePair
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card) :
    paperAxisProperEdgePair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) =
      paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralOppositeSide k)
        (Fin.cast (congrArg Finset.card
          (paperAxisProperEndpointSideCoordinates_eq_opposite g hg a ha hproject k)) i.rev) := by
  fin_cases k
  · simpa [paperAxisProperEndpointBoundarySortedTag,paperQuadrilateralOppositeSide,Fin.cast_rev] using
      paperAxisProperEndpointSortedTag_edgePair g hg a ha hproject 0 i
  · simpa [paperAxisProperEndpointBoundarySortedTag,paperQuadrilateralOppositeSide,Fin.cast_rev] using
      paperAxisProperEndpointSortedTag_edgePair g hg a ha hproject 1 i.rev
  · simpa [paperAxisProperEndpointBoundarySortedTag,paperQuadrilateralOppositeSide,Fin.cast_rev] using
      paperAxisProperEndpointSortedTag_edgePair g hg a ha hproject 2 i.rev
  · simpa [paperAxisProperEndpointBoundarySortedTag,paperQuadrilateralOppositeSide,Fin.cast_rev] using
      paperAxisProperEndpointSortedTag_edgePair g hg a ha hproject 3 i

/-- Every actual opposite-side EDGE pair has boundary ranks summing to
N_source-1, derived from literal actual sorted gluing, not a rank field. -/
theorem paperAxisProperEdgePair_actual_boundary_rank_sum
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralOppositeSide k)).card)
    (hpair : paperAxisProperEdgePair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) =
      paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralOppositeSide k) j) :
    i.val+j.val+1 = (paperAxisProperEndpointSideCoordinates g hg a ha k).card := by
  have he := paperAxisProperEndpointBoundarySortedTag_edgePair g hg a ha hproject k i
  rw [hpair] at he
  have hj := (paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha
    (paperQuadrilateralOppositeSide k)).injective
      (congrArg (paperAxisProperEndpointBoundaryCoordinate g hg a ha) he)
  have hv := congrArg Fin.val hj
  simp only [Fin.val_cast,Fin.val_rev] at hv
  have hi := i.isLt
  omega

end Markov
