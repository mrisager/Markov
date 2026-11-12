import Markov.PaperAxisOppositeRankCardinality
import Markov.PaperAxisOppositePartnerStrict

/-! The actual opposite-packet rank offset follows from actual geometric
partner reversal and an actual ARC equivalence of its finite tails/heads. -/
noncomputable section
open Set
namespace Markov

/-- Every actual opposite-side arc from sorted rank i on sidek to rankj on
Opposite k satisfies i+j+1=NextStart(k)+PrevStop(Opposite k). This is a
constructed actual matching identity, not a rotation or packet field. -/
theorem paperAxisOpposite_actual_partner_rank_sum
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralOppositeSide k)).card)
    (hpair : paperAxisProperArcEndpointPair g hg a
      (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) =
      paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralOppositeSide k) j) :
    i.val + j.val + 1 = paperAxisNextCornerPacketStart g hg a ha k +
      paperAxisPrevCornerPacketStop g hg a ha (paperQuadrilateralOppositeSide k) := by
  classical
  have hs := paperAxisProperEndpointBoundarySortedTag_side g hg a ha k i
  have ht := paperAxisProperEndpointBoundarySortedTag_side g hg a ha (paperQuadrilateralOppositeSide k) j
  have hp : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a
      (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) = paperQuadrilateralOppositeSide k := by
    rw [hpair]
    exact ht
  have hback : paperAxisProperArcEndpointPair g hg a
      (paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralOppositeSide k) j) =
      paperAxisProperEndpointBoundarySortedTag g hg a ha k i := by
    rw [← hpair, paperAxisProperArcEndpointPair_involutive]
  have hpt : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a
      (paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralOppositeSide k) j)) =
      paperQuadrilateralOppositeSide (paperQuadrilateralOppositeSide k) := by
    rw [hback,paperQuadrilateralOppositeSide_apply_apply]
    exact hs
  let E :
      {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k ∧
        paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) =
          paperQuadrilateralOppositeSide k ∧
        paperAxisProperEndpointBoundaryCoordinate g hg a ha
          (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) <
        paperAxisProperEndpointBoundaryCoordinate g hg a ha t} ≃
      {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t =
          paperQuadrilateralOppositeSide k ∧
        paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) =
          paperQuadrilateralOppositeSide (paperQuadrilateralOppositeSide k) ∧
        paperAxisProperEndpointBoundaryCoordinate g hg a ha t <
        paperAxisProperEndpointBoundaryCoordinate g hg a ha
          (paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralOppositeSide k) j)} :=
    Equiv.subtypeEquiv (paperAxisProperArcEndpointPair g hg a) (by
      intro t
      constructor
      · rintro ⟨ht0,ht1,hlt⟩
        have hn := paperAxisOppositePartner_boundary_strict g hg a ha hproject k _ t hs hp ht0 ht1 hlt
        refine ⟨ht1,?_,?_⟩
        · rw [paperAxisProperArcEndpointPair_involutive,paperQuadrilateralOppositeSide_apply_apply]
          exact ht0
        · simpa only [hpair] using hn
      · rintro ⟨ht0,ht1,hlt⟩
        have htside : paperAxisProperEndpointSide g hg a ha t = k := by
          simpa only [paperAxisProperArcEndpointPair_involutive g hg a t,
            paperQuadrilateralOppositeSide_apply_apply] using ht1
        have hn := paperAxisOppositePartner_boundary_strict g hg a ha hproject
          (paperQuadrilateralOppositeSide k) (paperAxisProperArcEndpointPair g hg a t)
          (paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralOppositeSide k) j)
          ht0 ht1 ht hpt hlt
        refine ⟨htside,ht0,?_⟩
        simpa only [hback,paperAxisProperArcEndpointPair_involutive g hg a t] using hn)
  have hc := Fintype.card_congr E
  rw [paperAxisOppositePacket_tail_card g hg a ha hproject k i hp,
    paperAxisOppositePacket_head_card g hg a ha hproject (paperQuadrilateralOppositeSide k) j hpt] at hc
  have hi := (paperAxisOppositePacket_iff_middle g hg a ha hproject k i).mp hp
  have hj := (paperAxisOppositePacket_iff_middle g hg a ha hproject (paperQuadrilateralOppositeSide k) j).mp hpt
  omega

/-- Every computed actual middle-packet source has its literal actual partner
at the forced opposite-side offset. No matching witness is an input. -/
theorem paperAxisOppositePacket_actual_partner_offset
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (hi : paperAxisPrevCornerPacketStop g hg a ha k ≤ i.val ∧
      i.val < paperAxisNextCornerPacketStart g hg a ha k) :
    ∃ j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralOppositeSide k)).card,
      paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) =
        paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralOppositeSide k) j ∧
      j.val = paperAxisNextCornerPacketStart g hg a ha k +
        paperAxisPrevCornerPacketStop g hg a ha (paperQuadrilateralOppositeSide k) - (i.val+1) := by
  classical
  have hp := (paperAxisOppositePacket_iff_middle g hg a ha hproject k i).mpr hi
  have hr : paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) ∈
      Set.range (paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralOppositeSide k)) := by
    rw [paperAxisProperEndpointBoundarySortedTag_range g hg a ha hproject (paperQuadrilateralOppositeSide k)]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
  obtain ⟨j,hj⟩ := hr
  have he := paperAxisOpposite_actual_partner_rank_sum g hg a ha hproject k i j hj.symm
  refine ⟨j,hj.symm,?_⟩
  omega

end Markov
