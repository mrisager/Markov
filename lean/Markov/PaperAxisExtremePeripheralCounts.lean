import Markov.PaperAxisExtremeEndpointSet
import Markov.PaperAxisProperSixArcCounts
import Mathlib.Data.Fintype.BigOperators

/-! Actual finite consequences of the actual extrema set being the whole
diagram. The extrema-set equality is an explicit input here; its geometric
ARC-closure proof belongs to a separate module. No peripheral layer or
classification field is assumed. -/
noncomputable section
open Set
open scoped BigOperators
namespace Markov

/-- If every actual tag is a side-coordinate extremum, actual coordinate
injectivity bounds each actual side fiber by two tags. -/
theorem paperAxisProperEndpointSideCount_le_two_of_all_extreme
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (hS : paperAxisExtremeEndpointSet g hg a ha = Set.univ) (k : Fin 4) :
    paperAxisProperEndpointSideCount g hg a ha k ≤ 2 := by
  classical
  let T := {t : paperAxisProperEndpointTag g hg a //
    paperAxisProperEndpointSide g hg a ha t = k}
  let isMin (t : T) : Prop := ∀ u, paperAxisProperEndpointSide g hg a ha u = k →
    paperAxisProperEndpointCoordinate g hg a ha t ≤ paperAxisProperEndpointCoordinate g hg a ha u
  let f (t : T) : Fin 2 := if isMin t then 0 else 1
  have hext (t : T) : isMin t ∨
      ∀ u, paperAxisProperEndpointSide g hg a ha u = k →
        paperAxisProperEndpointCoordinate g hg a ha u ≤ paperAxisProperEndpointCoordinate g hg a ha t := by
    have ht : t.val ∈ paperAxisExtremeEndpointSet g hg a ha := by rw [hS]; trivial
    simpa only [paperAxisExtremeEndpointSet, Set.mem_setOf_eq, t.property] using ht
  have hinj : Function.Injective f := by
    intro s t h
    have hc : paperAxisProperEndpointCoordinate g hg a ha s =
        paperAxisProperEndpointCoordinate g hg a ha t := by
      by_cases hs : isMin s
      · have ht : isMin t := by
          by_contra ht
          simp only [f, if_pos hs, if_neg ht] at h
          exact Fin.zero_ne_one h
        exact le_antisymm (hs t t.property) (ht s s.property)
      · have ht : ¬ isMin t := by
          intro ht
          simp only [f, if_neg hs, if_pos ht] at h
          exact Fin.zero_ne_one h.symm
        exact le_antisymm ((hext t).resolve_left ht s s.property)
          ((hext s).resolve_left hs t t.property)
    apply Subtype.ext
    apply paperAxisProperEndpointCoordinate_injOn_side g hg a ha hproject k
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, s.property⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.property⟩
    · exact hc
  have hcard := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_fin] using hcard

/-- Positive actual 01 and 12 corner counts, together with the actual
opposite-side balance, put at least two actual endpoints on every side.
If all tags are actual extrema, every actual side therefore has exactly two. -/
theorem paperAxisProperEndpointSideCount_eq_two_of_corner_positive_all_extreme
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (hS : paperAxisExtremeEndpointSet g hg a ha = Set.univ)
    (h01 : 0 < paperAxisProperArcSixCount g hg a ha 0)
    (h12 : 0 < paperAxisProperArcSixCount g hg a ha 1) (k : Fin 4) :
    paperAxisProperEndpointSideCount g hg a ha k = 2 := by
  have hu (j : Fin 4) := paperAxisProperEndpointSideCount_le_two_of_all_extreme g hg a ha hproject hS j
  have hf := paperAxisProperEndpointSideCount_six_formulas g hg a ha
  have hb := paperAxisProperArcSixCount_corner_balance g hg a ha hproject
  have h0 : paperAxisProperEndpointSideCount g hg a ha 0 = 2 := by have := hu 0; omega
  have h1 : paperAxisProperEndpointSideCount g hg a ha 1 = 2 := by have := hu 1; omega
  have h2 : paperAxisProperEndpointSideCount g hg a ha 2 = 2 := by have := hu 2; omega
  have h3 : paperAxisProperEndpointSideCount g hg a ha 3 = 2 := by have := hu 3; omega
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- The actual six arc counts are exactly one of each corner and no
opposite-side arc. This is derived from actual incidence equations, not
assumed as a peripheral packet field. -/
theorem paperAxisProperArcSixCount_eq_corner_ones_of_all_extreme
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (hS : paperAxisExtremeEndpointSet g hg a ha = Set.univ)
    (h01 : 0 < paperAxisProperArcSixCount g hg a ha 0)
    (h12 : 0 < paperAxisProperArcSixCount g hg a ha 1) (r : Fin 6) :
    paperAxisProperArcSixCount g hg a ha r = ![1,1,1,1,0,0] r := by
  have h0 := paperAxisProperEndpointSideCount_eq_two_of_corner_positive_all_extreme
    g hg a ha hproject hS h01 h12 0
  have h1 := paperAxisProperEndpointSideCount_eq_two_of_corner_positive_all_extreme
    g hg a ha hproject hS h01 h12 1
  have hf := paperAxisProperEndpointSideCount_six_formulas g hg a ha
  have hb := paperAxisProperArcSixCount_corner_balance g hg a ha hproject
  have hc : paperAxisProperArcSixCount g hg a ha 0 = 1 ∧
      paperAxisProperArcSixCount g hg a ha 1 = 1 ∧
      paperAxisProperArcSixCount g hg a ha 2 = 1 ∧
      paperAxisProperArcSixCount g hg a ha 3 = 1 ∧
      paperAxisProperArcSixCount g hg a ha 4 = 0 ∧
      paperAxisProperArcSixCount g hg a ha 5 = 0 := by omega
  fin_cases r
  · exact hc.1
  · exact hc.2.1
  · exact hc.2.2.1
  · exact hc.2.2.2.1
  · exact hc.2.2.2.2.1
  · exact hc.2.2.2.2.2

/-- The four actual side fibers partition all actual tagged endpoints. -/
theorem paperAxisProperEndpointTag_card_eq_sideCount_sum
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) :
    Fintype.card (paperAxisProperEndpointTag g hg a) =
      ∑ k : Fin 4, paperAxisProperEndpointSideCount g hg a ha k := by
  classical
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv
    (paperAxisProperEndpointSide g hg a ha)), Fintype.card_sigma]
  rfl

/-- The genuine all-extrema diagram with both corner families positive has
exactly eight actual endpoint tags. -/
theorem paperAxisProperEndpointTag_card_eight_of_corner_positive_all_extreme
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (hS : paperAxisExtremeEndpointSet g hg a ha = Set.univ)
    (h01 : 0 < paperAxisProperArcSixCount g hg a ha 0)
    (h12 : 0 < paperAxisProperArcSixCount g hg a ha 1) :
    Fintype.card (paperAxisProperEndpointTag g hg a) = 8 := by
  rw [paperAxisProperEndpointTag_card_eq_sideCount_sum g hg a ha]
  simp_rw [paperAxisProperEndpointSideCount_eq_two_of_corner_positive_all_extreme
    g hg a ha hproject hS h01 h12]
  norm_num

/-- The actual cyclic itinerary then has exactly four actual letters. No
word identification with a commutator is asserted by this count theorem. -/
theorem paperAxisPeriodCellWord_length_four_of_corner_positive_all_extreme
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (hS : paperAxisExtremeEndpointSet g hg a ha = Set.univ)
    (h01 : 0 < paperAxisProperArcSixCount g hg a ha 0)
    (h12 : 0 < paperAxisProperArcSixCount g hg a ha 1) :
    (paperAxisPeriodCellWord g hg a).length = 4 := by
  have hc := paperAxisProperEndpointTag_card_eight_of_corner_positive_all_extreme
    g hg a ha hproject hS h01 h12
  rw [paperAxisProperEndpointTag_card] at hc
  omega

end Markov
