import Markov.PaperAxisActualPacketPartition
import Mathlib.Order.Interval.Finset.Nat

/-! Actual opposite-packet tails and heads are counted using the actual
complete rank table, not an assumed partner-rank field. -/
noncomputable section
open Set
namespace Markov

private def oppositeTailEquiv
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (hi : paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperQuadrilateralOppositeSide k) :
    (Finset.Ico (i.val+1) (paperAxisNextCornerPacketStart g hg a ha k) : Finset ℕ) ≃
    {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k ∧
      paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) =
        paperQuadrilateralOppositeSide k ∧
      paperAxisProperEndpointBoundaryCoordinate g hg a ha
        (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) <
      paperAxisProperEndpointBoundaryCoordinate g hg a ha t} := by
  classical
  have hm := (paperAxisOppositePacket_iff_middle g hg a ha hproject k i).mp hi
  have hbound := paperAxisNextCornerPacketStart_le_card g hg a ha k
  let f : (Finset.Ico (i.val+1) (paperAxisNextCornerPacketStart g hg a ha k) : Finset ℕ) →
      {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k ∧
        paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) =
          paperQuadrilateralOppositeSide k ∧
        paperAxisProperEndpointBoundaryCoordinate g hg a ha
          (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) <
        paperAxisProperEndpointBoundaryCoordinate g hg a ha t} := fun n => by
    have hn := Finset.mem_Ico.mp n.property
    let j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card :=
      ⟨n.val,lt_of_lt_of_le hn.2 hbound⟩
    have hij : i < j := by change i.val < n.val; omega
    refine ⟨paperAxisProperEndpointBoundarySortedTag g hg a ha k j,
      paperAxisProperEndpointBoundarySortedTag_side g hg a ha k j, ?_,
      paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k hij⟩
    apply (paperAxisOppositePacket_iff_middle g hg a ha hproject k j).mpr
    change paperAxisPrevCornerPacketStop g hg a ha k ≤ n.val ∧
      n.val < paperAxisNextCornerPacketStart g hg a ha k
    exact ⟨by omega,hn.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro n m he
    apply Subtype.ext
    have hc := congrArg (paperAxisProperEndpointBoundaryCoordinate g hg a ha)
      (congrArg Subtype.val he)
    have hi' := (paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k).injective hc
    exact congrArg Fin.val hi'
  · intro t
    have hr : t.val ∈ Set.range (paperAxisProperEndpointBoundarySortedTag g hg a ha k) := by
      rw [paperAxisProperEndpointBoundarySortedTag_range g hg a ha hproject k]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,t.property.1⟩
    obtain ⟨j,hj⟩ := hr
    have ho : paperAxisProperEndpointSide g hg a ha
        (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k j)) =
          paperQuadrilateralOppositeSide k := by rw [hj]; exact t.property.2.1
    have hjm := (paperAxisOppositePacket_iff_middle g hg a ha hproject k j).mp ho
    have hlt : i < j := (paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k).lt_iff_lt.mp
      (by simpa only [hj] using t.property.2.2)
    have hn : j.val ∈ Finset.Ico (i.val+1) (paperAxisNextCornerPacketStart g hg a ha k) :=
      Finset.mem_Ico.mpr ⟨by have := (show i.val < j.val from hlt); omega,hjm.2⟩
    exact ⟨⟨j.val,hn⟩, Subtype.ext hj⟩

private def oppositeHeadEquiv
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (hi : paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperQuadrilateralOppositeSide k) :
    (Finset.Ico (paperAxisPrevCornerPacketStop g hg a ha k) i.val : Finset ℕ) ≃
    {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k ∧
      paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) =
        paperQuadrilateralOppositeSide k ∧
      paperAxisProperEndpointBoundaryCoordinate g hg a ha t <
      paperAxisProperEndpointBoundaryCoordinate g hg a ha
        (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)} := by
  classical
  have hm := (paperAxisOppositePacket_iff_middle g hg a ha hproject k i).mp hi
  let f : (Finset.Ico (paperAxisPrevCornerPacketStop g hg a ha k) i.val : Finset ℕ) →
      {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k ∧
        paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) =
          paperQuadrilateralOppositeSide k ∧
        paperAxisProperEndpointBoundaryCoordinate g hg a ha t <
        paperAxisProperEndpointBoundaryCoordinate g hg a ha
          (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)} := fun n => by
    have hn := Finset.mem_Ico.mp n.property
    let j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card :=
      ⟨n.val,lt_trans hn.2 i.isLt⟩
    have hji : j < i := hn.2
    refine ⟨paperAxisProperEndpointBoundarySortedTag g hg a ha k j,
      paperAxisProperEndpointBoundarySortedTag_side g hg a ha k j, ?_,
      paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k hji⟩
    apply (paperAxisOppositePacket_iff_middle g hg a ha hproject k j).mpr
    change paperAxisPrevCornerPacketStop g hg a ha k ≤ n.val ∧
      n.val < paperAxisNextCornerPacketStart g hg a ha k
    exact ⟨hn.1,lt_trans hn.2 hm.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro n m he
    apply Subtype.ext
    have hc := congrArg (paperAxisProperEndpointBoundaryCoordinate g hg a ha)
      (congrArg Subtype.val he)
    have hi' := (paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k).injective hc
    exact congrArg Fin.val hi'
  · intro t
    have hr : t.val ∈ Set.range (paperAxisProperEndpointBoundarySortedTag g hg a ha k) := by
      rw [paperAxisProperEndpointBoundarySortedTag_range g hg a ha hproject k]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,t.property.1⟩
    obtain ⟨j,hj⟩ := hr
    have ho : paperAxisProperEndpointSide g hg a ha
        (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k j)) =
          paperQuadrilateralOppositeSide k := by rw [hj]; exact t.property.2.1
    have hjm := (paperAxisOppositePacket_iff_middle g hg a ha hproject k j).mp ho
    have hlt : j < i := (paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k).lt_iff_lt.mp
      (by simpa only [hj] using t.property.2.2)
    have hn : j.val ∈ Finset.Ico (paperAxisPrevCornerPacketStop g hg a ha k) i.val :=
      Finset.mem_Ico.mpr ⟨hjm.1,hlt⟩
    exact ⟨⟨j.val,hn⟩, Subtype.ext hj⟩

/-- The actual opposite-packet tags strictly after an actual rank have the
literal finite tail cardinality, proved by their actual complete enumeration. -/
theorem paperAxisOppositePacket_tail_card
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (hi : paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperQuadrilateralOppositeSide k) :
    Fintype.card {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k ∧
      paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) =
        paperQuadrilateralOppositeSide k ∧
      paperAxisProperEndpointBoundaryCoordinate g hg a ha
        (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) <
      paperAxisProperEndpointBoundaryCoordinate g hg a ha t} =
      paperAxisNextCornerPacketStart g hg a ha k - (i.val+1) := by
  classical
  rw [← Fintype.card_congr (oppositeTailEquiv g hg a ha hproject k i hi),
    Fintype.card_coe, Nat.card_Ico]

/-- The actual opposite-packet tags strictly before an actual rank have the
literal finite head cardinality. No matching or packet cardinality is assumed. -/
theorem paperAxisOppositePacket_head_card
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (hi : paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperQuadrilateralOppositeSide k) :
    Fintype.card {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k ∧
      paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) =
        paperQuadrilateralOppositeSide k ∧
      paperAxisProperEndpointBoundaryCoordinate g hg a ha t <
      paperAxisProperEndpointBoundaryCoordinate g hg a ha
        (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)} =
      i.val - paperAxisPrevCornerPacketStop g hg a ha k := by
  classical
  rw [← Fintype.card_congr (oppositeHeadEquiv g hg a ha hproject k i hi),
    Fintype.card_coe, Nat.card_Ico]

end Markov
