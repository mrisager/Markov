import Markov.PaperAxisPacketCutCounts
import Markov.PaperOppositeArcExclusion

/-! Literal cyclic side indices and actual packet parameters at ANY selected
corner. These are reindexings of actual original sides, not Q homeomorphisms. -/
noncomputable section
open Set
namespace Markov

theorem paperQuadrilateralNextSide_apply_twice (k : Fin 4) :
    paperQuadrilateralNextSide (paperQuadrilateralNextSide k) = paperQuadrilateralOppositeSide k := by
  fin_cases k <;> rfl

theorem paperQuadrilateralOppositeNextSide (k : Fin 4) :
    paperQuadrilateralOppositeSide (paperQuadrilateralNextSide k) = paperQuadrilateralNextSide.symm k := by
  fin_cases k <;> rfl

theorem paperQuadrilateralOppositePrevSide (k : Fin 4) :
    paperQuadrilateralOppositeSide (paperQuadrilateralNextSide.symm k) = paperQuadrilateralNextSide k := by
  fin_cases k <;> rfl

theorem paperQuadrilateralPrevSide_apply_twice (k : Fin 4) :
    paperQuadrilateralNextSide.symm (paperQuadrilateralNextSide.symm k) = paperQuadrilateralOppositeSide k := by
  fin_cases k <;> rfl

/-- Actual opposite-corner member counts agree at every literal selected
side. The actual opposite endpoint balance supplies this identity. -/
theorem paperAxisProperArcPairCount_corner_balance
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4) :
    paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide k) =
        paperAxisProperArcPairCount g hg a ha (paperQuadrilateralOppositeSide k) (paperQuadrilateralNextSide.symm k) ∧
    paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide.symm k) =
        paperAxisProperArcPairCount g hg a ha (paperQuadrilateralNextSide k) (paperQuadrilateralOppositeSide k) := by
  have hb := paperAxisProperArcSixCount_corner_balance g hg a ha hproject
  change paperAxisProperArcPairCount g hg a ha 0 1 = paperAxisProperArcPairCount g hg a ha 2 3 ∧
    paperAxisProperArcPairCount g hg a ha 1 2 = paperAxisProperArcPairCount g hg a ha 3 0 at hb
  fin_cases k
  · change paperAxisProperArcPairCount g hg a ha 0 1 = paperAxisProperArcPairCount g hg a ha 2 3 ∧
      paperAxisProperArcPairCount g hg a ha 0 3 = paperAxisProperArcPairCount g hg a ha 1 2
    exact ⟨hb.1,(paperAxisProperArcPairCount_comm g hg a ha 0 3).trans hb.2.symm⟩
  · change paperAxisProperArcPairCount g hg a ha 1 2 = paperAxisProperArcPairCount g hg a ha 3 0 ∧
      paperAxisProperArcPairCount g hg a ha 1 0 = paperAxisProperArcPairCount g hg a ha 2 3
    exact ⟨hb.2,(paperAxisProperArcPairCount_comm g hg a ha 1 0).trans hb.1⟩
  · change paperAxisProperArcPairCount g hg a ha 2 3 = paperAxisProperArcPairCount g hg a ha 0 1 ∧
      paperAxisProperArcPairCount g hg a ha 2 1 = paperAxisProperArcPairCount g hg a ha 3 0
    exact ⟨hb.1.symm,(paperAxisProperArcPairCount_comm g hg a ha 2 1).trans hb.2⟩
  · change paperAxisProperArcPairCount g hg a ha 3 0 = paperAxisProperArcPairCount g hg a ha 1 2 ∧
      paperAxisProperArcPairCount g hg a ha 3 2 = paperAxisProperArcPairCount g hg a ha 0 1
    exact ⟨hb.2.symm,(paperAxisProperArcPairCount_comm g hg a ha 3 2).trans hb.1.symm⟩

private theorem actualCyclicOpposite_zero
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4) :
    paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralOppositeSide k) = 0 ∨
      paperAxisProperArcPairCount g hg a ha (paperQuadrilateralNextSide.symm k) (paperQuadrilateralNextSide k) = 0 := by
  have h := Nat.mul_eq_zero.mp (paperAxisProperArc_opposite_pairCount_mul_eq_zero g hg a ha hproject)
  fin_cases k
  · change paperAxisProperArcPairCount g hg a ha 0 2 = 0 ∨ paperAxisProperArcPairCount g hg a ha 3 1 = 0
    rw [paperAxisProperArcPairCount_comm g hg a ha 3 1]
    exact h
  · change paperAxisProperArcPairCount g hg a ha 1 3 = 0 ∨ paperAxisProperArcPairCount g hg a ha 0 2 = 0
    exact h.symm
  · change paperAxisProperArcPairCount g hg a ha 2 0 = 0 ∨ paperAxisProperArcPairCount g hg a ha 1 3 = 0
    rw [paperAxisProperArcPairCount_comm g hg a ha 2 0]
    exact h
  · change paperAxisProperArcPairCount g hg a ha 3 1 = 0 ∨ paperAxisProperArcPairCount g hg a ha 2 0 = 0
    rw [paperAxisProperArcPairCount_comm g hg a ha 3 1,paperAxisProperArcPairCount_comm g hg a ha 2 0]
    exact h.symm

/-- At any actual sidek with no previous-corner members, every required cut
and side length is derived from ACTUAL A/E/F member counts, with E=0 orF=0
proved by actual opposite-arc crossing. No rotation/packet parameter is given. -/
theorem paperAxisCyclic_missing_corner_actual_parameters
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (hB : paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide.symm k) = 0) :
    (paperAxisProperEndpointSideCoordinates g hg a ha k).card =
        paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide k) +
          paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralOppositeSide k) ∧
    (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card =
        paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide k) +
          paperAxisProperArcPairCount g hg a ha (paperQuadrilateralNextSide.symm k) (paperQuadrilateralNextSide k) ∧
    (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide k)).card =
        (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card ∧
    paperAxisPrevCornerPacketStop g hg a ha k = 0 ∧
    paperAxisNextCornerPacketStart g hg a ha k = paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralOppositeSide k) ∧
    paperAxisPrevCornerPacketStop g hg a ha (paperQuadrilateralOppositeSide k) = 0 ∧
    paperAxisPrevCornerPacketStop g hg a ha (paperQuadrilateralNextSide.symm k) =
      paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide k) ∧
    paperAxisNextCornerPacketStart g hg a ha (paperQuadrilateralNextSide.symm k) =
      (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card ∧
    paperAxisPrevCornerPacketStop g hg a ha (paperQuadrilateralNextSide k) =
      paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide k) ∧
    (paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralOppositeSide k) = 0 ∨
      paperAxisProperArcPairCount g hg a ha (paperQuadrilateralNextSide.symm k) (paperQuadrilateralNextSide k) = 0) := by
  have hb := paperAxisProperArcPairCount_corner_balance g hg a ha hproject k
  have hpK := paperAxisPrevCornerPacket_length_eq_pairCount g hg a ha hproject k
  have hnK := paperAxisNextCornerPacket_length_eq_pairCount g hg a ha hproject k
  have hoK := paperAxisOppositePacket_length_eq_pairCount g hg a ha hproject k
  have hpP := paperAxisPrevCornerPacket_length_eq_pairCount g hg a ha hproject (paperQuadrilateralNextSide.symm k)
  rw [paperQuadrilateralPrevSide_apply_twice] at hpP
  have hnP := paperAxisNextCornerPacket_length_eq_pairCount g hg a ha hproject (paperQuadrilateralNextSide.symm k)
  rw [paperQuadrilateralNextSide.apply_symm_apply k] at hnP
  have hoP := paperAxisOppositePacket_length_eq_pairCount g hg a ha hproject (paperQuadrilateralNextSide.symm k)
  rw [paperQuadrilateralOppositePrevSide] at hoP
  have hPrevOpp : paperQuadrilateralNextSide.symm (paperQuadrilateralOppositeSide k) = paperQuadrilateralNextSide k := by
    rw [← paperQuadrilateralNextSide_apply_twice,paperQuadrilateralNextSide.symm_apply_apply]
  have hpO := paperAxisPrevCornerPacket_length_eq_pairCount g hg a ha hproject (paperQuadrilateralOppositeSide k)
  rw [hPrevOpp] at hpO
  have hpN := paperAxisPrevCornerPacket_length_eq_pairCount g hg a ha hproject (paperQuadrilateralNextSide k)
  rw [paperQuadrilateralNextSide.symm_apply_apply k] at hpN
  have hcPO := paperAxisProperArcPairCount_comm g hg a ha (paperQuadrilateralNextSide.symm k) (paperQuadrilateralOppositeSide k)
  have hcPK := paperAxisProperArcPairCount_comm g hg a ha (paperQuadrilateralNextSide.symm k) k
  have hcON := paperAxisProperArcPairCount_comm g hg a ha (paperQuadrilateralOppositeSide k) (paperQuadrilateralNextSide k)
  have hcNK := paperAxisProperArcPairCount_comm g hg a ha (paperQuadrilateralNextSide k) k
  have hboundK := paperAxisNextCornerPacketStart_le_card g hg a ha k
  have hboundP := paperAxisNextCornerPacketStart_le_card g hg a ha (paperQuadrilateralNextSide.symm k)
  have horderedP := paperAxisPrevCornerPacketStop_le_nextStart g hg a ha hproject (paperQuadrilateralNextSide.symm k)
  have hcard := congrArg Finset.card (paperAxisProperEndpointSideCoordinates_eq_opposite g hg a ha hproject (paperQuadrilateralNextSide.symm k))
  rw [paperQuadrilateralOppositePrevSide] at hcard
  have hzero := actualCyclicOpposite_zero g hg a ha hproject k
  omega

end Markov
