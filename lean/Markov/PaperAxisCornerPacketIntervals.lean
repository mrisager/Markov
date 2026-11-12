import Markov.PaperAxisAllCornersNearest
import Mathlib.Data.Finset.Max

/-! Computed actual rank intervals of the corner packets. The interval
properties follow from genuine nearer-corner geometry, not packet fields. -/
noncomputable section
open Set
namespace Markov

/-- A larger actual source-side rank above a next-corner arc stays in that
corner packet, and its actual partner lies strictly earlier on the next side. -/
theorem paperAxisNextCornerPacket_rank_strict
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (hi : paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperQuadrilateralNextSide k) (hij : i < j) :
    paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k j)) =
        paperQuadrilateralNextSide k ∧
    paperAxisProperEndpointBoundaryCoordinate g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k j)) <
    paperAxisProperEndpointBoundaryCoordinate g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) :=
  paperAxisCorner_source_nearer_partner g hg a ha hproject k _ _
    (paperAxisProperEndpointBoundarySortedTag_side g hg a ha k i) hi
    (paperAxisProperEndpointBoundarySortedTag_side g hg a ha k j)
    (paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k hij)

/-- The actual next-side corner packet is upward closed in actual boundary ranks. -/
theorem paperAxisNextCornerPacket_final
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (hi : paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperQuadrilateralNextSide k) (hij : i ≤ j) :
    paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k j)) =
        paperQuadrilateralNextSide k := by
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact (paperAxisNextCornerPacket_rank_strict g hg a ha hproject k i j hi hlt).1
  · exact hi

/-- A smaller actual rank below a previous-corner arc stays in that packet;
its partner lies strictly later on the previous side. -/
theorem paperAxisPrevCornerPacket_rank_strict
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (hj : paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k j)) =
        paperQuadrilateralNextSide.symm k) (hij : i < j) :
    paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperQuadrilateralNextSide.symm k ∧
    paperAxisProperEndpointBoundaryCoordinate g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k j)) <
    paperAxisProperEndpointBoundaryCoordinate g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) := by
  have hpp : paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a
        (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k j))) =
        paperQuadrilateralNextSide (paperQuadrilateralNextSide.symm k) := by
    rw [paperAxisProperArcEndpointPair_involutive, Equiv.apply_symm_apply]
    exact paperAxisProperEndpointBoundarySortedTag_side g hg a ha k j
  have ht : paperAxisProperEndpointSide g hg a ha
      (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) =
        paperQuadrilateralNextSide (paperQuadrilateralNextSide.symm k) := by
    rw [Equiv.apply_symm_apply]
    exact paperAxisProperEndpointBoundarySortedTag_side g hg a ha k i
  have hlt : paperAxisProperEndpointBoundaryCoordinate g hg a ha
      (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) <
      paperAxisProperEndpointBoundaryCoordinate g hg a ha
        (paperAxisProperArcEndpointPair g hg a
          (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k j))) := by
    rw [paperAxisProperArcEndpointPair_involutive]
    exact paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k hij
  exact paperAxisCorner_next_nearer_partner g hg a ha hproject (paperQuadrilateralNextSide.symm k)
    _ _ hj hpp ht hlt

/-- The actual previous-side corner packet is downward closed in actual ranks. -/
theorem paperAxisPrevCornerPacket_initial
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (hj : paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k j)) =
        paperQuadrilateralNextSide.symm k) (hij : i ≤ j) :
    paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperQuadrilateralNextSide.symm k := by
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact (paperAxisPrevCornerPacket_rank_strict g hg a ha hproject k i j hj hlt).1
  · exact hj

/-- The actual next-corner packet's first rank, or the actual side length
if no actual next-corner tag exists. This is computed from actual ARC data. -/
def paperAxisNextCornerPacketStart
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) : ℕ := by
  classical
  let S := Finset.univ.filter (fun i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card =>
    paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperQuadrilateralNextSide k)
  exact if h : S.Nonempty then (S.min' h).val else
    (paperAxisProperEndpointSideCoordinates g hg a ha k).card

/-- One past the actual previous-corner packet's last rank, or zero when
that actual packet is empty. No interval hypothesis enters this definition. -/
def paperAxisPrevCornerPacketStop
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) : ℕ := by
  classical
  let S := Finset.univ.filter (fun i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card =>
    paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperQuadrilateralNextSide.symm k)
  exact if h : S.Nonempty then (S.max' h).val + 1 else 0

/-- Genuine geometry proves that the computed actual next packet is EXACTLY
the final rank interval, including the empty-packet case. -/
theorem paperAxisNextCornerPacket_iff_start_le
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card) :
    paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperQuadrilateralNextSide k ↔
      paperAxisNextCornerPacketStart g hg a ha k ≤ i.val := by
  classical
  let S := Finset.univ.filter (fun j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card =>
    paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k j)) =
        paperQuadrilateralNextSide k)
  change _ ↔ (if h : S.Nonempty then (S.min' h).val else _) ≤ i.val
  by_cases h : S.Nonempty
  · rw [dif_pos h]
    have hm : S.min' h ∈ S := Finset.min'_mem S h
    have hmin := (Finset.mem_filter.mp hm).2
    constructor
    · intro hi
      exact Finset.min'_le S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
    · intro hi
      exact paperAxisNextCornerPacket_final g hg a ha hproject k (S.min' h) i hmin hi
  · rw [dif_neg h]
    constructor
    · intro hi
      exact (h ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩).elim
    · intro hi
      exact (Nat.not_le_of_gt i.isLt hi).elim

/-- The computed actual previous packet is EXACTLY the initial rank interval. -/
theorem paperAxisPrevCornerPacket_iff_lt_stop
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card) :
    paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) =
        paperQuadrilateralNextSide.symm k ↔
      i.val < paperAxisPrevCornerPacketStop g hg a ha k := by
  classical
  let S := Finset.univ.filter (fun j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card =>
    paperAxisProperEndpointSide g hg a ha
      (paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k j)) =
        paperQuadrilateralNextSide.symm k)
  change _ ↔ i.val < (if h : S.Nonempty then (S.max' h).val + 1 else 0)
  by_cases h : S.Nonempty
  · rw [dif_pos h]
    have hm : S.max' h ∈ S := Finset.max'_mem S h
    have hmax := (Finset.mem_filter.mp hm).2
    constructor
    · intro hi
      have hl := Finset.le_max' S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
      exact Nat.lt_succ_of_le hl
    · intro hi
      exact paperAxisPrevCornerPacket_initial g hg a ha hproject k i (S.max' h) hmax
        (Nat.le_of_lt_succ hi)
  · rw [dif_neg h]
    constructor
    · intro hi
      exact (h ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩).elim
    · intro hi
      exact (Nat.not_lt_zero _ hi).elim

end Markov
