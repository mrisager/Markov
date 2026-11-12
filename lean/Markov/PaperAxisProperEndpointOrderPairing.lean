import Markov.PaperAxisProperEndpointOrder
import Markov.PaperAxisOppositeEndpointCounts

/-! Actual edge-pairing preserves the actual coordinate sets and actual
sorted ranks on opposite original sides. This is derived from genuine actual
quotient gluing, not an order-preserving matching premise. -/
noncomputable section
open Set
namespace Markov

/-- Opposite actual sides have exactly the same finite actual free-coordinate
set, by the genuinely constructed edge permutation and its coordinate law. -/
theorem paperAxisProperEndpointSideCoordinates_eq_opposite
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) (k : Fin 4) :
    paperAxisProperEndpointSideCoordinates g hg a ha k =
      paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralOppositeSide k) := by
  classical
  have hsub (k : Fin 4) : paperAxisProperEndpointSideCoordinates g hg a ha k ⊆
      paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralOppositeSide k) := by
    intro r hr
    obtain ⟨t, ht, htr⟩ := Finset.mem_image.mp hr
    have htk : paperAxisProperEndpointSide g hg a ha t = k := (Finset.mem_filter.mp ht).2
    have he := paperAxisProperEdgePair_opposite_and_coordinate g hg a ha hproject t
    have hu : paperAxisProperEdgePair g hg a t ∈
        paperAxisProperEndpointSideTags g hg a ha (paperQuadrilateralOppositeSide k) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, he.1.trans (congrArg paperQuadrilateralOppositeSide htk)⟩
    have hc : paperAxisProperEndpointCoordinate g hg a ha t =
        paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperEdgePair g hg a t) := he.2
    exact Finset.mem_image.mpr ⟨_, hu, hc.symm.trans htr⟩
  apply Finset.Subset.antisymm (hsub k)
  simpa only [paperQuadrilateralOppositeSide_apply_apply] using hsub (paperQuadrilateralOppositeSide k)

private theorem orderEmbOfFin_cast_eq (S T : Finset ℝ) (h : S = T) (i : Fin S.card) :
    S.orderEmbOfFin rfl i = T.orderEmbOfFin rfl (Fin.cast (congrArg Finset.card h) i) := by
  subst T
  rfl

/-- The genuine edge permutation pairs precisely equal-ranked actual sorted
endpoints on opposite sides, with the literal cardinality cast displayed. -/
theorem paperAxisProperEndpointSortedTag_edgePair
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card) :
    paperAxisProperEdgePair g hg a (paperAxisProperEndpointSortedTag g hg a ha k i) =
      paperAxisProperEndpointSortedTag g hg a ha (paperQuadrilateralOppositeSide k)
        (Fin.cast (congrArg Finset.card
          (paperAxisProperEndpointSideCoordinates_eq_opposite g hg a ha hproject k)) i) := by
  classical
  let j := Fin.cast (congrArg Finset.card
    (paperAxisProperEndpointSideCoordinates_eq_opposite g hg a ha hproject k)) i
  let t := paperAxisProperEndpointSortedTag g hg a ha k i
  have ht : t ∈ paperAxisProperEndpointSideTags g hg a ha k :=
    (paperAxisProperEndpointSortedTag_spec g hg a ha k i).1
  have htk : paperAxisProperEndpointSide g hg a ha t = k := (Finset.mem_filter.mp ht).2
  have he := paperAxisProperEdgePair_opposite_and_coordinate g hg a ha hproject t
  have hu : paperAxisProperEdgePair g hg a t ∈
      paperAxisProperEndpointSideTags g hg a ha (paperQuadrilateralOppositeSide k) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, he.1.trans (congrArg paperQuadrilateralOppositeSide htk)⟩
  have ho : paperAxisProperEndpointSideOrder g hg a ha k i =
      paperAxisProperEndpointSideOrder g hg a ha (paperQuadrilateralOppositeSide k) j :=
    orderEmbOfFin_cast_eq _ _ (paperAxisProperEndpointSideCoordinates_eq_opposite g hg a ha hproject k) i
  apply paperAxisProperEndpointCoordinate_injOn_side g hg a ha hproject
    (paperQuadrilateralOppositeSide k) hu
    (paperAxisProperEndpointSortedTag_spec g hg a ha (paperQuadrilateralOppositeSide k) j).1
  calc
    paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperEdgePair g hg a t) =
        paperAxisProperEndpointCoordinate g hg a ha t := he.2.symm
    _ = paperAxisProperEndpointSideOrder g hg a ha k i :=
      (paperAxisProperEndpointSortedTag_spec g hg a ha k i).2
    _ = paperAxisProperEndpointSideOrder g hg a ha (paperQuadrilateralOppositeSide k) j := ho
    _ = paperAxisProperEndpointCoordinate g hg a ha
        (paperAxisProperEndpointSortedTag g hg a ha (paperQuadrilateralOppositeSide k) j) :=
      (paperAxisProperEndpointSortedTag_spec g hg a ha (paperQuadrilateralOppositeSide k) j).2.symm

end Markov
