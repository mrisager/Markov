import Markov.PaperAxisCornerPacketMatching
import Markov.PaperAxisOppositePacketMatching
import Markov.PaperAxisBoundaryEdgeRanks

/-! Literal actual EDGE-after-ARC pairing has three computed rank-translation
branches. Reduction to one global interval rotation is a separate theorem. -/
noncomputable section
open Set
namespace Markov

private theorem actualBoundaryEdgeTarget
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card) :
    ∃ j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralOppositeSide k)).card,
      paperAxisProperEdgePair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) =
        paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralOppositeSide k) j ∧
      i.val+j.val+1 = (paperAxisProperEndpointSideCoordinates g hg a ha k).card := by
  let j := Fin.cast (congrArg Finset.card
    (paperAxisProperEndpointSideCoordinates_eq_opposite g hg a ha hproject k)) i.rev
  have hj := paperAxisProperEndpointBoundarySortedTag_edgePair g hg a ha hproject k i
  refine ⟨j,hj,?_⟩
  exact paperAxisProperEdgePair_actual_boundary_rank_sum g hg a ha hproject k i j hj

/-- On the computed actual next-corner final interval, literal EDGE-after-ARC
lands on Opposite(Next k) and has rank l+N_k=i+N_next. All actual tags and
target bounds are constructed, with no interval-exchange witness supplied. -/
theorem paperAxisPacketStep_next_translation
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (hi : paperAxisNextCornerPacketStart g hg a ha k ≤ i.val) :
    ∃ l : Fin (paperAxisProperEndpointSideCoordinates g hg a ha
        (paperQuadrilateralOppositeSide (paperQuadrilateralNextSide k))).card,
      paperAxisProperEdgePair g hg a (paperAxisProperArcEndpointPair g hg a
        (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperAxisProperEndpointBoundarySortedTag g hg a ha
          (paperQuadrilateralOppositeSide (paperQuadrilateralNextSide k)) l ∧
      l.val + (paperAxisProperEndpointSideCoordinates g hg a ha k).card =
        i.val + (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide k)).card := by
  obtain ⟨j,hj,_⟩ := paperAxisNextCornerPacket_actual_partner_offset g hg a ha hproject k i hi
  have hc := paperAxisCorner_actual_partner_rank_sum g hg a ha hproject k i j hj
  obtain ⟨l,hl,he⟩ := actualBoundaryEdgeTarget g hg a ha hproject (paperQuadrilateralNextSide k) j
  refine ⟨l,?_,?_⟩
  · rw [hj]
    exact hl
  · omega

/-- On the computed actual previous-corner initial interval, literal
EDGE-after-ARC preserves the source rank and lands on Opposite(Previous k). -/
theorem paperAxisPacketStep_prev_translation
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (hi : i.val < paperAxisPrevCornerPacketStop g hg a ha k) :
    ∃ l : Fin (paperAxisProperEndpointSideCoordinates g hg a ha
        (paperQuadrilateralOppositeSide (paperQuadrilateralNextSide.symm k))).card,
      paperAxisProperEdgePair g hg a (paperAxisProperArcEndpointPair g hg a
        (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperAxisProperEndpointBoundarySortedTag g hg a ha
          (paperQuadrilateralOppositeSide (paperQuadrilateralNextSide.symm k)) l ∧
      l.val = i.val := by
  classical
  have hp := (paperAxisPrevCornerPacket_iff_lt_stop g hg a ha hproject k i).mpr hi
  have hr : paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) ∈
      Set.range (paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralNextSide.symm k)) := by
    rw [paperAxisProperEndpointBoundarySortedTag_range g hg a ha hproject (paperQuadrilateralNextSide.symm k)]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
  obtain ⟨j,hj⟩ := hr
  have hback : paperAxisProperArcEndpointPair g hg a
      (paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralNextSide.symm k) j) =
      paperAxisProperEndpointBoundarySortedTag g hg a ha k i := by
    rw [hj,paperAxisProperArcEndpointPair_involutive]
  have hsum : ∀ u : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card,
      paperAxisProperArcEndpointPair g hg a
          (paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralNextSide.symm k) j) =
        paperAxisProperEndpointBoundarySortedTag g hg a ha k u →
      j.val+u.val+1 =
        (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card := by
    have hfun := paperAxisCorner_actual_partner_rank_sum g hg a ha hproject (paperQuadrilateralNextSide.symm k) j
    rw [paperQuadrilateralNextSide.apply_symm_apply k] at hfun
    exact hfun
  have hc := hsum i hback
  obtain ⟨l,hl,he⟩ := actualBoundaryEdgeTarget g hg a ha hproject (paperQuadrilateralNextSide.symm k) j
  refine ⟨l,?_,?_⟩
  · rw [← hj]
    exact hl
  · omega

/-- On the computed actual opposite-side middle interval, literal
EDGE-after-ARC returns to the same side and translates ranks by the forced
cut/cardinality offset. A global single-rotation coding is not asserted here. -/
theorem paperAxisPacketStep_opposite_translation
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (hi : paperAxisPrevCornerPacketStop g hg a ha k ≤ i.val ∧
      i.val < paperAxisNextCornerPacketStart g hg a ha k) :
    ∃ l : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card,
      paperAxisProperEdgePair g hg a (paperAxisProperArcEndpointPair g hg a
        (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperAxisProperEndpointBoundarySortedTag g hg a ha k l ∧
      l.val + paperAxisNextCornerPacketStart g hg a ha k +
          paperAxisPrevCornerPacketStop g hg a ha (paperQuadrilateralOppositeSide k) =
        i.val + (paperAxisProperEndpointSideCoordinates g hg a ha k).card := by
  obtain ⟨j,hj,_⟩ := paperAxisOppositePacket_actual_partner_offset g hg a ha hproject k i hi
  have hc := paperAxisOpposite_actual_partner_rank_sum g hg a ha hproject k i j hj
  obtain ⟨l,hl,he⟩ := actualBoundaryEdgeTarget g hg a ha hproject (paperQuadrilateralOppositeSide k) j
  have hcard := congrArg Finset.card (paperAxisProperEndpointSideCoordinates_eq_opposite g hg a ha hproject k)
  have hout : ∃ l : Fin (paperAxisProperEndpointSideCoordinates g hg a ha
        (paperQuadrilateralOppositeSide (paperQuadrilateralOppositeSide k))).card,
      paperAxisProperEdgePair g hg a (paperAxisProperArcEndpointPair g hg a
        (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperAxisProperEndpointBoundarySortedTag g hg a ha
          (paperQuadrilateralOppositeSide (paperQuadrilateralOppositeSide k)) l ∧
      l.val + paperAxisNextCornerPacketStart g hg a ha k +
          paperAxisPrevCornerPacketStop g hg a ha (paperQuadrilateralOppositeSide k) =
        i.val + (paperAxisProperEndpointSideCoordinates g hg a ha k).card := by
    refine ⟨l,?_,?_⟩
    · rw [hj]
      exact hl
    · omega
  rw [paperQuadrilateralOppositeSide_apply_apply k] at hout
  exact hout

end Markov
