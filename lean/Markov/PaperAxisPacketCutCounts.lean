import Markov.PaperAxisActualPacketPartition
import Markov.PaperAxisProperSixArcCounts
import Mathlib.Order.Interval.Finset.Nat

/-! The computed actual packet cuts equal actual geometric arc counts.
No packet-length or count-parameter field is an input. -/
noncomputable section
open Set
namespace Markov

/-- Actual tags on sidek whose genuine ARC partner is on sidel are in
bijection with the actual unordered kl member arcs. -/
theorem paperAxisActualPartnerSide_tag_card_eq_pairCount
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k l : Fin 4) :
    Fintype.card {t : paperAxisProperEndpointTag g hg a //
      paperAxisProperEndpointSide g hg a ha t = k ∧
      paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) = l} =
      paperAxisProperArcPairCount g hg a ha k l := by
  classical
  let f : {t : paperAxisProperEndpointTag g hg a //
      paperAxisProperEndpointSide g hg a ha t = k ∧
      paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) = l} →
    {i : paperAxisProperArcIndex g hg a //
      (paperAxisProperEndpointSide g hg a ha (i,0) = k ∧ paperAxisProperEndpointSide g hg a ha (i,1) = l) ∨
      (paperAxisProperEndpointSide g hg a ha (i,0) = l ∧ paperAxisProperEndpointSide g hg a ha (i,1) = k)} :=
    fun t => ⟨t.val.1, by
      rcases t with ⟨⟨i,e⟩,ht⟩
      fin_cases e
      · left
        change paperAxisProperEndpointSide g hg a ha (i,0) = k ∧
          paperAxisProperEndpointSide g hg a ha (i,1) = l at ht
        exact ht
      · right
        change paperAxisProperEndpointSide g hg a ha (i,1) = k ∧
          paperAxisProperEndpointSide g hg a ha (i,0) = l at ht
        exact ⟨ht.2,ht.1⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro s t he
      have hi : s.val.1 = t.val.1 := congrArg Subtype.val he
      apply Subtype.ext
      by_contra hne
      exact paperAxisProperEndpoint_same_side_arcIndex_ne g hg a ha s.val t.val hne
        (s.property.1.trans t.property.1.symm) hi
    · rintro ⟨i,hi⟩
      rcases hi with ⟨hk,hl⟩ | ⟨hl,hk⟩
      · have ht : paperAxisProperEndpointSide g hg a ha (i,0) = k ∧
            paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a (i,0)) = l := by
          change paperAxisProperEndpointSide g hg a ha (i,0) = k ∧
            paperAxisProperEndpointSide g hg a ha (i,1) = l
          exact ⟨hk,hl⟩
        exact ⟨⟨(i,0),ht⟩,Subtype.ext rfl⟩
      · have ht : paperAxisProperEndpointSide g hg a ha (i,1) = k ∧
            paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a (i,1)) = l := by
          change paperAxisProperEndpointSide g hg a ha (i,1) = k ∧
            paperAxisProperEndpointSide g hg a ha (i,0) = l
          exact ⟨hk,hl⟩
        exact ⟨⟨(i,1),ht⟩,Subtype.ext rfl⟩
  exact Fintype.card_congr (Equiv.ofBijective f hf)

private def actualPartnerIntervalEquiv
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k l : Fin 4)
    (lo hi : ℕ) (hhi : hi ≤ (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (hiff : ∀ i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card,
      paperAxisProperEndpointSide g hg a ha
        (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) = l ↔
      lo ≤ i.val ∧ i.val < hi) :
    (Finset.Ico lo hi : Finset ℕ) ≃
    {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k ∧
      paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) = l} := by
  classical
  let f : ↥(Finset.Ico lo hi : Finset ℕ) →
      {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k ∧
        paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) = l} := fun n => by
    have hn := Finset.mem_Ico.mp n.property
    let i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card :=
      ⟨n.val,lt_of_lt_of_le hn.2 hhi⟩
    exact ⟨paperAxisProperEndpointBoundarySortedTag g hg a ha k i,
      paperAxisProperEndpointBoundarySortedTag_side g hg a ha k i,(hiff i).mpr hn⟩
  apply Equiv.ofBijective f
  constructor
  · intro n m he
    apply Subtype.ext
    have hc := congrArg (paperAxisProperEndpointBoundaryCoordinate g hg a ha)
      (congrArg Subtype.val he)
    exact congrArg Fin.val ((paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k).injective hc)
  · intro t
    have hr : t.val ∈ Set.range (paperAxisProperEndpointBoundarySortedTag g hg a ha k) := by
      rw [paperAxisProperEndpointBoundarySortedTag_range g hg a ha hproject k]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,t.property.1⟩
    obtain ⟨i,hi'⟩ := hr
    have hp : paperAxisProperEndpointSide g hg a ha
        (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) = l := by
      rw [hi']
      exact t.property.2
    have hm := (hiff i).mp hp
    exact ⟨⟨i.val,Finset.mem_Ico.mpr hm⟩,Subtype.ext hi'⟩

private theorem actualPartnerIntervalCard
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k l : Fin 4)
    (lo hi : ℕ) (hhi : hi ≤ (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (hiff : ∀ i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card,
      paperAxisProperEndpointSide g hg a ha
        (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) = l ↔
      lo ≤ i.val ∧ i.val < hi) :
    hi-lo = paperAxisProperArcPairCount g hg a ha k l := by
  have hc := Fintype.card_congr (actualPartnerIntervalEquiv g hg a ha hproject k l lo hi hhi hiff)
  rw [Fintype.card_coe,Nat.card_Ico,paperAxisActualPartnerSide_tag_card_eq_pairCount] at hc
  exact hc

/-- The actual next-corner final interval has length equal to the actual
unordered corner-member count, so its computed start is parametrized genuinely. -/
theorem paperAxisNextCornerPacket_length_eq_pairCount
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4) :
    (paperAxisProperEndpointSideCoordinates g hg a ha k).card - paperAxisNextCornerPacketStart g hg a ha k =
      paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide k) := by
  apply actualPartnerIntervalCard g hg a ha hproject k (paperQuadrilateralNextSide k)
    (paperAxisNextCornerPacketStart g hg a ha k) _ (le_refl _)
  intro i
  exact (paperAxisNextCornerPacket_iff_start_le g hg a ha hproject k i).trans
    ⟨fun hi => ⟨hi,i.isLt⟩,fun hi => hi.1⟩

/-- The actual previous-corner initial interval has length exactly the
corresponding actual unordered corner-member count. -/
theorem paperAxisPrevCornerPacket_length_eq_pairCount
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4) :
    paperAxisPrevCornerPacketStop g hg a ha k =
      paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide.symm k) := by
  have hc := actualPartnerIntervalCard g hg a ha hproject k (paperQuadrilateralNextSide.symm k)
    0 (paperAxisPrevCornerPacketStop g hg a ha k) (paperAxisPrevCornerPacketStop_le_card g hg a ha k)
    (fun i => (paperAxisPrevCornerPacket_iff_lt_stop g hg a ha hproject k i).trans
      ⟨fun hi => ⟨Nat.zero_le _,hi⟩,fun hi => hi.2⟩)
  simpa only [Nat.sub_zero] using hc

/-- The actual opposite-side middle interval has length exactly the actual
opposite-member count, with no packet-count field supplied. -/
theorem paperAxisOppositePacket_length_eq_pairCount
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4) :
    paperAxisNextCornerPacketStart g hg a ha k - paperAxisPrevCornerPacketStop g hg a ha k =
      paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralOppositeSide k) :=
  actualPartnerIntervalCard g hg a ha hproject k (paperQuadrilateralOppositeSide k)
    (paperAxisPrevCornerPacketStop g hg a ha k) (paperAxisNextCornerPacketStart g hg a ha k)
    (paperAxisNextCornerPacketStart_le_card g hg a ha k)
    (paperAxisOppositePacket_iff_middle g hg a ha hproject k)

end Markov
