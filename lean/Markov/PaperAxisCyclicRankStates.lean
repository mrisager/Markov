import Markov.PaperAxisActualPacketPartition

/-! A literal finite state table of actual tags: reverse the actual sidek
list, followed by the reversed actual the previous side list. No traversal model is assumed. -/
noncomputable section
open Set
namespace Markov

private theorem cyclic_k_ne_prev (k : Fin 4) : k ≠ paperQuadrilateralNextSide.symm k := by
  fin_cases k <;> decide

/-- The actual literal all-corner state table, made from the actual sorted endpoint
lists. Its size and entries are computed, not supplied as abstract data. -/
def paperAxisCyclicRankStateTag
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4)
    (r : Fin ((paperAxisProperEndpointSideCoordinates g hg a ha k).card +
      (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card)) :
    paperAxisProperEndpointTag g hg a :=
  if h : r.val < (paperAxisProperEndpointSideCoordinates g hg a ha k).card then
    paperAxisProperEndpointBoundarySortedTag g hg a ha k (⟨r.val,h⟩ : Fin _).rev
  else
    paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralNextSide.symm k)
      (⟨r.val-(paperAxisProperEndpointSideCoordinates g hg a ha k).card,
        by have := r.isLt; omega⟩ : Fin _).rev

/-- The computed state table has its literal side label on each block. -/
theorem paperAxisCyclicRankStateTag_side
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4)
    (r : Fin ((paperAxisProperEndpointSideCoordinates g hg a ha k).card +
      (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card)) :
    paperAxisProperEndpointSide g hg a ha (paperAxisCyclicRankStateTag g hg a ha k r) =
      if r.val < (paperAxisProperEndpointSideCoordinates g hg a ha k).card then k else (paperQuadrilateralNextSide.symm k) := by
  unfold paperAxisCyclicRankStateTag
  split_ifs <;> exact paperAxisProperEndpointBoundarySortedTag_side g hg a ha _ _

/-- The actual state table loses no endpoint: every entry is a different
actual tag, proved using actual side labels and actual strict side sorting. -/
theorem paperAxisCyclicRankStateTag_injective
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) :
    Function.Injective (paperAxisCyclicRankStateTag g hg a ha k) := by
  intro r s he
  have hrs := r.isLt
  have hss := s.isLt
  by_cases hr : r.val < (paperAxisProperEndpointSideCoordinates g hg a ha k).card
  · by_cases hs : s.val < (paperAxisProperEndpointSideCoordinates g hg a ha k).card
    · simp only [paperAxisCyclicRankStateTag,dif_pos hr,dif_pos hs] at he
      have hi := (paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k).injective
        (congrArg (paperAxisProperEndpointBoundaryCoordinate g hg a ha) he)
      have hv := congrArg Fin.val hi
      simp only [Fin.val_rev] at hv
      apply Fin.ext
      omega
    · have hx := congrArg (paperAxisProperEndpointSide g hg a ha) he
      rw [paperAxisCyclicRankStateTag_side,paperAxisCyclicRankStateTag_side,if_pos hr,if_neg hs] at hx
      exact (cyclic_k_ne_prev k) hx |>.elim
  · by_cases hs : s.val < (paperAxisProperEndpointSideCoordinates g hg a ha k).card
    · have hx := congrArg (paperAxisProperEndpointSide g hg a ha) he
      rw [paperAxisCyclicRankStateTag_side,paperAxisCyclicRankStateTag_side,if_neg hr,if_pos hs] at hx
      exact (fun h => cyclic_k_ne_prev k h.symm) hx |>.elim
    · simp only [paperAxisCyclicRankStateTag,dif_neg hr,dif_neg hs] at he
      have hi := (paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha (paperQuadrilateralNextSide.symm k)).injective
        (congrArg (paperAxisProperEndpointBoundaryCoordinate g hg a ha) he)
      have hv := congrArg Fin.val hi
      simp only [Fin.val_rev] at hv
      apply Fin.ext
      omega

/-- Its actual range is exactly the genuine sidek-or-the previous side endpoint tags.
Completeness follows from the already proved actual side enumeration. -/
theorem paperAxisCyclicRankStateTag_range
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) :
    Set.range (paperAxisCyclicRankStateTag g hg a ha k) =
      {t | paperAxisProperEndpointSide g hg a ha t = k ∨
        paperAxisProperEndpointSide g hg a ha t = (paperQuadrilateralNextSide.symm k)} := by
  classical
  ext t
  constructor
  · rintro ⟨r,rfl⟩
    change paperAxisProperEndpointSide g hg a ha (paperAxisCyclicRankStateTag g hg a ha k r) = k ∨
      paperAxisProperEndpointSide g hg a ha (paperAxisCyclicRankStateTag g hg a ha k r) = (paperQuadrilateralNextSide.symm k)
    simp only [paperAxisCyclicRankStateTag_side]
    split_ifs <;> simp
  · rintro (ht | ht)
    · have hx : t ∈ Set.range (paperAxisProperEndpointBoundarySortedTag g hg a ha k) := by
        rw [paperAxisProperEndpointBoundarySortedTag_range g hg a ha hproject k]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩
      obtain ⟨i,hi⟩ := hx
      let r : Fin ((paperAxisProperEndpointSideCoordinates g hg a ha k).card +
          (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card) :=
        ⟨i.rev.val,lt_of_lt_of_le i.rev.isLt (Nat.le_add_right _ _)⟩
      have hr : r.val < (paperAxisProperEndpointSideCoordinates g hg a ha k).card := i.rev.isLt
      refine ⟨r,?_⟩
      rw [paperAxisCyclicRankStateTag,dif_pos hr]
      have he : (⟨r.val,hr⟩ : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card) = i.rev :=
        Fin.ext rfl
      rw [he,Fin.rev_rev]
      exact hi
    · have hx : t ∈ Set.range (paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralNextSide.symm k)) := by
        rw [paperAxisProperEndpointBoundarySortedTag_range g hg a ha hproject (paperQuadrilateralNextSide.symm k)]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩
      obtain ⟨i,hi⟩ := hx
      let r : Fin ((paperAxisProperEndpointSideCoordinates g hg a ha k).card +
          (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card) :=
        ⟨(paperAxisProperEndpointSideCoordinates g hg a ha k).card+i.rev.val,
          Nat.add_lt_add_left i.rev.isLt _⟩
      have hr : ¬ r.val < (paperAxisProperEndpointSideCoordinates g hg a ha k).card := by
        dsimp only [r]
        omega
      refine ⟨r,?_⟩
      rw [paperAxisCyclicRankStateTag,dif_neg hr]
      have he : (⟨r.val-(paperAxisProperEndpointSideCoordinates g hg a ha k).card,
          by have := r.isLt; omega⟩ : Fin (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card) = i.rev := by
        apply Fin.ext
        exact Nat.add_sub_cancel_left _ _
      rw [he,Fin.rev_rev]
      exact hi

end Markov
