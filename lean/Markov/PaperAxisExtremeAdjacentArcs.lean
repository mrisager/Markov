import Markov.PaperAxisExtremePeripheralCounts

/-! Actual adjacent-side arcs derived from the vanishing actual opposite
arc counts. This does not identify the cyclic word or its free class. -/
noncomputable section
open Set
namespace Markov

private theorem fourSides_adjacent
    (x y : Fin 4) (hne : x ≠ y)
    (h02 : ¬ ((x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0)))
    (h13 : ¬ ((x = 1 ∧ y = 3) ∨ (x = 3 ∧ y = 1))) :
    y = x + 1 ∨ x = y + 1 := by
  revert x y
  decide

/-- If the actual 02 and 13 member counts vanish, each actual proper-family
arc joins two literal adjacent original sides. An actual opposite-side member
would contribute to its actual positive count, so no matching field is used. -/
theorem paperAxisProperArc_adjacent_sides_of_opposite_counts_zero
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (h02 : paperAxisProperArcPairCount g hg a ha 0 2 = 0)
    (h13 : paperAxisProperArcPairCount g hg a ha 1 3 = 0)
    (i : paperAxisProperArcIndex g hg a) :
    paperAxisProperEndpointSide g hg a ha (i,1) =
        paperAxisProperEndpointSide g hg a ha (i,0) + 1 ∨
      paperAxisProperEndpointSide g hg a ha (i,0) =
        paperAxisProperEndpointSide g hg a ha (i,1) + 1 := by
  apply fourSides_adjacent _ _ (paperAxisProperArc_endpointSide_ne g hg a ha i)
  · intro hi
    have hp := (paperAxisProperArcPairCount_pos_iff g hg a ha 0 2).mpr ⟨i,hi⟩
    omega
  · intro hi
    have hp := (paperAxisProperArcPairCount_pos_iff g hg a ha 1 3).mpr ⟨i,hi⟩
    omega

/-- The positive-corner all-extrema diagram has only actual adjacent-side
arcs; the opposite counts are derived from its proved actual incidences. -/
theorem paperAxisProperArc_adjacent_sides_of_corner_positive_all_extreme
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (hS : paperAxisExtremeEndpointSet g hg a ha = Set.univ)
    (h01 : 0 < paperAxisProperArcSixCount g hg a ha 0)
    (h12 : 0 < paperAxisProperArcSixCount g hg a ha 1)
    (i : paperAxisProperArcIndex g hg a) :
    paperAxisProperEndpointSide g hg a ha (i,1) =
        paperAxisProperEndpointSide g hg a ha (i,0) + 1 ∨
      paperAxisProperEndpointSide g hg a ha (i,0) =
        paperAxisProperEndpointSide g hg a ha (i,1) + 1 := by
  have h02 := paperAxisProperArcSixCount_eq_corner_ones_of_all_extreme
    g hg a ha hproject hS h01 h12 4
  have h13 := paperAxisProperArcSixCount_eq_corner_ones_of_all_extreme
    g hg a ha hproject hS h01 h12 5
  change paperAxisProperArcPairCount g hg a ha 0 2 = 0 at h02
  change paperAxisProperArcPairCount g hg a ha 1 3 = 0 at h13
  exact paperAxisProperArc_adjacent_sides_of_opposite_counts_zero g hg a ha h02 h13 i

/-- The actual ARC involution exchanges adjacent side labels in this actual
finite diagram, for either orientation of every actual tagged endpoint. -/
theorem paperAxisProperArcEndpointPair_adjacent_of_corner_positive_all_extreme
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (hS : paperAxisExtremeEndpointSet g hg a ha = Set.univ)
    (h01 : 0 < paperAxisProperArcSixCount g hg a ha 0)
    (h12 : 0 < paperAxisProperArcSixCount g hg a ha 1)
    (t : paperAxisProperEndpointTag g hg a) :
    paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) =
        paperAxisProperEndpointSide g hg a ha t + 1 ∨
      paperAxisProperEndpointSide g hg a ha t =
        paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) + 1 := by
  rcases t with ⟨i,e⟩
  have hi := paperAxisProperArc_adjacent_sides_of_corner_positive_all_extreme
    g hg a ha hproject hS h01 h12 i
  fin_cases e
  · change paperAxisProperEndpointSide g hg a ha (i,1) =
        paperAxisProperEndpointSide g hg a ha (i,0) + 1 ∨
      paperAxisProperEndpointSide g hg a ha (i,0) =
        paperAxisProperEndpointSide g hg a ha (i,1) + 1
    exact hi
  · change paperAxisProperEndpointSide g hg a ha (i,0) =
        paperAxisProperEndpointSide g hg a ha (i,1) + 1 ∨
      paperAxisProperEndpointSide g hg a ha (i,1) =
        paperAxisProperEndpointSide g hg a ha (i,0) + 1
    exact hi.symm

end Markov
