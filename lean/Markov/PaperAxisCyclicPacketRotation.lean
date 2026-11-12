import Markov.PaperAxisCyclicRankStates
import Markov.PaperAxisCyclicPacketParameters
import Markov.PaperAxisPacketStepTranslations

/-! One ACTUAL modular-rotation model at every selected literal side with
an empty previous-corner packet. Opposite-family exclusion is discharged
geometrically in the actual parameter theorem, not supplied as a model field. -/
noncomputable section
open Set
namespace Markov

private theorem cyclic_mod_shift (N P r : ℕ) (hr : r < N+P) (hP : P ≤ r) :
    (r+N)%(N+P) = r-P := by
  rw [show r+N = (r-P)+(N+P) by omega,Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- At ANY selected original sidek with no actual previous-corner members,
the computed injective actual Sidek/Prevk table intertwines literal
EDGE-after-ARC with ONE modular rotation by the actual sidek cardinality. -/
theorem paperAxisCyclic_missing_corner_actual_rotation
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (hB : paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide.symm k) = 0)
    (r : Fin ((paperAxisProperEndpointSideCoordinates g hg a ha k).card +
      (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card)) :
    paperAxisProperEdgePair g hg a (paperAxisProperArcEndpointPair g hg a
      (paperAxisCyclicRankStateTag g hg a ha k r)) =
      paperAxisCyclicRankStateTag g hg a ha k
        ⟨(r.val+(paperAxisProperEndpointSideCoordinates g hg a ha k).card)%
          ((paperAxisProperEndpointSideCoordinates g hg a ha k).card+
            (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card),
          Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) r.isLt)⟩ := by
  let N := (paperAxisProperEndpointSideCoordinates g hg a ha k).card
  let P := (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card
  let A := paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide k)
  let E := paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralOppositeSide k)
  let F := paperAxisProperArcPairCount g hg a ha (paperQuadrilateralNextSide.symm k) (paperQuadrilateralNextSide k)
  have hrlt : r.val < N+P := r.isLt
  let R : Fin (N+P) := ⟨(r.val+N)%(N+P),Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) hrlt)⟩
  change _ = paperAxisCyclicRankStateTag g hg a ha k R
  obtain ⟨hN,hP,hNext,hStopK,hStartK,hStopO,hStopP,hStartP,hStopNext,hzero⟩ :=
    paperAxisCyclic_missing_corner_actual_parameters g hg a ha hproject k hB
  change N = A+E at hN
  change P = A+F at hP
  change E=0 ∨ F=0 at hzero
  by_cases rp : r.val < P
  · have hRv : R.val = r.val+N := Nat.mod_eq_of_lt (by omega)
    have hR : ¬ R.val < N := by omega
    by_cases hr : r.val < N
    · let i : Fin N := ⟨r.val,hr⟩
      have hi : paperAxisNextCornerPacketStart g hg a ha k ≤ i.rev.val := by
        rw [hStartK]
        change E ≤ N-(r.val+1)
        omega
      have ht := paperAxisPacketStep_next_translation g hg a ha hproject k i.rev hi
      rw [paperQuadrilateralOppositeNextSide k] at ht
      obtain ⟨l,hl,hRank⟩ := ht
      change l.val+N = (N-(r.val+1))+(paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide k)).card at hRank
      rw [paperAxisCyclicRankStateTag,dif_pos hr,hl,paperAxisCyclicRankStateTag,dif_neg hR]
      apply congrArg (paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralNextSide.symm k))
      apply Fin.ext
      change l.val = P-((R.val-N)+1)
      omega
    · let i : Fin P := ⟨r.val-N,by omega⟩
      have hi : paperAxisPrevCornerPacketStop g hg a ha (paperQuadrilateralNextSide.symm k) ≤ i.rev.val ∧
          i.rev.val < paperAxisNextCornerPacketStart g hg a ha (paperQuadrilateralNextSide.symm k) := by
        rw [hStopP,hStartP]
        change A ≤ P-((r.val-N)+1) ∧ P-((r.val-N)+1) < P
        omega
      have ht := paperAxisPacketStep_opposite_translation g hg a ha hproject (paperQuadrilateralNextSide.symm k) i.rev hi
      rw [paperQuadrilateralOppositePrevSide k] at ht
      obtain ⟨l,hl,hRank⟩ := ht
      change l.val+paperAxisNextCornerPacketStart g hg a ha (paperQuadrilateralNextSide.symm k)+
          paperAxisPrevCornerPacketStop g hg a ha (paperQuadrilateralNextSide k) =
        (P-((r.val-N)+1))+P at hRank
      rw [paperAxisCyclicRankStateTag,dif_neg hr,hl,paperAxisCyclicRankStateTag,dif_neg hR]
      apply congrArg (paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralNextSide.symm k))
      apply Fin.ext
      change l.val = P-((R.val-N)+1)
      omega
  · have hRv : R.val = r.val-P := cyclic_mod_shift N P r.val hrlt (Nat.le_of_not_gt rp)
    have hR : R.val < N := by omega
    by_cases hr : r.val < N
    · let i : Fin N := ⟨r.val,hr⟩
      have hi : paperAxisPrevCornerPacketStop g hg a ha k ≤ i.rev.val ∧
          i.rev.val < paperAxisNextCornerPacketStart g hg a ha k := by
        rw [hStopK,hStartK]
        change 0 ≤ N-(r.val+1) ∧ N-(r.val+1) < E
        omega
      obtain ⟨l,hl,hRank⟩ := paperAxisPacketStep_opposite_translation g hg a ha hproject k i.rev hi
      change l.val+paperAxisNextCornerPacketStart g hg a ha k+
          paperAxisPrevCornerPacketStop g hg a ha (paperQuadrilateralOppositeSide k) =
        (N-(r.val+1))+N at hRank
      rw [paperAxisCyclicRankStateTag,dif_pos hr,hl,paperAxisCyclicRankStateTag,dif_pos hR]
      apply congrArg (paperAxisProperEndpointBoundarySortedTag g hg a ha k)
      apply Fin.ext
      change l.val = N-(R.val+1)
      omega
    · let i : Fin P := ⟨r.val-N,by omega⟩
      have hi : i.rev.val < paperAxisPrevCornerPacketStop g hg a ha (paperQuadrilateralNextSide.symm k) := by
        rw [hStopP]
        change P-((r.val-N)+1) < A
        omega
      have ht := paperAxisPacketStep_prev_translation g hg a ha hproject (paperQuadrilateralNextSide.symm k) i.rev hi
      rw [paperQuadrilateralPrevSide_apply_twice k,paperQuadrilateralOppositeSide_apply_apply k] at ht
      obtain ⟨l,hl,hRank⟩ := ht
      change l.val = P-((r.val-N)+1) at hRank
      rw [paperAxisCyclicRankStateTag,dif_neg hr,hl,paperAxisCyclicRankStateTag,dif_pos hR]
      apply congrArg (paperAxisProperEndpointBoundarySortedTag g hg a ha k)
      apply Fin.ext
      change l.val = N-(R.val+1)
      omega

/-- The literal actual ARC target label of the same all-k state table is
NextSide k below the actual previous-side cardinality threshold and Opposite k
otherwise. Together with the rotation this supplies actual signed coding. -/
theorem paperAxisCyclic_missing_corner_actual_letter
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (hB : paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide.symm k) = 0)
    (r : Fin ((paperAxisProperEndpointSideCoordinates g hg a ha k).card +
      (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card)) :
    paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a
      (paperAxisCyclicRankStateTag g hg a ha k r)) =
      if r.val < (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card
        then paperQuadrilateralNextSide k else paperQuadrilateralOppositeSide k := by
  let N := (paperAxisProperEndpointSideCoordinates g hg a ha k).card
  let P := (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card
  let A := paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide k)
  let E := paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralOppositeSide k)
  let F := paperAxisProperArcPairCount g hg a ha (paperQuadrilateralNextSide.symm k) (paperQuadrilateralNextSide k)
  have hrlt : r.val < N+P := r.isLt
  obtain ⟨hN,hP,_,hStopK,hStartK,_,hStopP,hStartP,_,hzero⟩ :=
    paperAxisCyclic_missing_corner_actual_parameters g hg a ha hproject k hB
  change N = A+E at hN
  change P = A+F at hP
  change E=0 ∨ F=0 at hzero
  by_cases rp : r.val < P
  · by_cases hr : r.val < N
    · let i : Fin N := ⟨r.val,hr⟩
      have hi : paperAxisNextCornerPacketStart g hg a ha k ≤ i.rev.val := by
        rw [hStartK]
        change E ≤ N-(r.val+1)
        omega
      rw [if_pos rp,paperAxisCyclicRankStateTag,dif_pos hr]
      exact (paperAxisNextCornerPacket_iff_start_le g hg a ha hproject k i.rev).mpr hi
    · let i : Fin P := ⟨r.val-N,by omega⟩
      have hi : paperAxisPrevCornerPacketStop g hg a ha (paperQuadrilateralNextSide.symm k) ≤ i.rev.val ∧
          i.rev.val < paperAxisNextCornerPacketStart g hg a ha (paperQuadrilateralNextSide.symm k) := by
        rw [hStopP,hStartP]
        change A ≤ P-((r.val-N)+1) ∧ P-((r.val-N)+1) < P
        omega
      have hp := (paperAxisOppositePacket_iff_middle g hg a ha hproject (paperQuadrilateralNextSide.symm k) i.rev).mpr hi
      rw [paperQuadrilateralOppositePrevSide k] at hp
      rw [if_pos rp,paperAxisCyclicRankStateTag,dif_neg hr]
      exact hp
  · by_cases hr : r.val < N
    · let i : Fin N := ⟨r.val,hr⟩
      have hi : paperAxisPrevCornerPacketStop g hg a ha k ≤ i.rev.val ∧
          i.rev.val < paperAxisNextCornerPacketStart g hg a ha k := by
        rw [hStopK,hStartK]
        change 0 ≤ N-(r.val+1) ∧ N-(r.val+1) < E
        omega
      rw [if_neg rp,paperAxisCyclicRankStateTag,dif_pos hr]
      exact (paperAxisOppositePacket_iff_middle g hg a ha hproject k i.rev).mpr hi
    · let i : Fin P := ⟨r.val-N,by omega⟩
      have hi : i.rev.val < paperAxisPrevCornerPacketStop g hg a ha (paperQuadrilateralNextSide.symm k) := by
        rw [hStopP]
        change P-((r.val-N)+1) < A
        omega
      have hp := (paperAxisPrevCornerPacket_iff_lt_stop g hg a ha hproject (paperQuadrilateralNextSide.symm k) i.rev).mpr hi
      rw [paperQuadrilateralPrevSide_apply_twice k] at hp
      rw [if_neg rp,paperAxisCyclicRankStateTag,dif_neg hr]
      exact hp

end Markov
