import Markov.PaperAxisCornerPacketIntervals

/-! The actual side ranks split into previous-corner, opposite-side and
next-corner intervals. All cuts are computed from the genuine ARC pairing. -/
noncomputable section
open Set
namespace Markov

/-- The computed next-packet start never exceeds the actual side length. -/
theorem paperAxisNextCornerPacketStart_le_card
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) :
    paperAxisNextCornerPacketStart g hg a ha k ≤
      (paperAxisProperEndpointSideCoordinates g hg a ha k).card := by
  classical
  unfold paperAxisNextCornerPacketStart
  dsimp only
  split_ifs
  · exact Nat.le_of_lt (Fin.isLt _)
  · exact le_rfl

/-- The computed previous-packet stop never exceeds the actual side length. -/
theorem paperAxisPrevCornerPacketStop_le_card
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) :
    paperAxisPrevCornerPacketStop g hg a ha k ≤
      (paperAxisProperEndpointSideCoordinates g hg a ha k).card := by
  classical
  unfold paperAxisPrevCornerPacketStop
  dsimp only
  split_ifs
  · exact Nat.succ_le_of_lt (Fin.isLt _)
  · exact Nat.zero_le _

/-- Actual initial and final corner packets cannot overlap: their genuine
partner-side labels differ. Thus their computed cuts are correctly ordered. -/
theorem paperAxisPrevCornerPacketStop_le_nextStart
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4) :
    paperAxisPrevCornerPacketStop g hg a ha k ≤ paperAxisNextCornerPacketStart g hg a ha k := by
  by_contra h
  have hlt := lt_of_not_ge h
  have hcard := paperAxisPrevCornerPacketStop_le_card g hg a ha k
  let i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card :=
    ⟨paperAxisNextCornerPacketStart g hg a ha k, lt_of_lt_of_le hlt hcard⟩
  have hn := (paperAxisNextCornerPacket_iff_start_le g hg a ha hproject k i).mpr (le_refl _)
  have hp := (paperAxisPrevCornerPacket_iff_lt_stop g hg a ha hproject k i).mpr hlt
  have hne : paperQuadrilateralNextSide k ≠ paperQuadrilateralNextSide.symm k := by
    fin_cases k <;> decide
  exact hne (hn.symm.trans hp)

private theorem actualSide_opposite_iff (k p : Fin 4) (hne : p ≠ k) :
    p = paperQuadrilateralOppositeSide k ↔
      p ≠ paperQuadrilateralNextSide.symm k ∧ p ≠ paperQuadrilateralNextSide k := by
  revert k p
  decide

/-- The actual opposite-side packet is EXACTLY the remaining middle interval.
This follows from the two genuine corner intervals and the actual distinct-side
property; no opposite-packet or global rotation field is supplied. -/
theorem paperAxisOppositePacket_iff_middle
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card) :
    paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperQuadrilateralOppositeSide k ↔
      paperAxisPrevCornerPacketStop g hg a ha k ≤ i.val ∧
        i.val < paperAxisNextCornerPacketStart g hg a ha k := by
  have hne : paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) ≠ k := by
    have hn := paperAxisProperArcEndpointPair_sides_ne g hg a ha
      (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)
    simpa only [paperAxisProperEndpointBoundarySortedTag_side] using hn
  rw [actualSide_opposite_iff _ _ hne]
  constructor
  · rintro ⟨hp,hn⟩
    exact ⟨Nat.le_of_not_gt (fun hi => hp
      ((paperAxisPrevCornerPacket_iff_lt_stop g hg a ha hproject k i).mpr hi)),
      Nat.lt_of_not_ge (fun hi => hn
      ((paperAxisNextCornerPacket_iff_start_le g hg a ha hproject k i).mpr hi))⟩
  · rintro ⟨hp,hn⟩
    exact ⟨fun he => (Nat.not_lt_of_ge hp)
      ((paperAxisPrevCornerPacket_iff_lt_stop g hg a ha hproject k i).mp he),
      fun he => (Nat.not_le_of_gt hn)
      ((paperAxisNextCornerPacket_iff_start_le g hg a ha hproject k i).mp he)⟩

end Markov
