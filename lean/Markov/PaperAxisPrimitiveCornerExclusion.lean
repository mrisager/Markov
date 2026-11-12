import Markov.PaperAxisFourArcParity
import Markov.PaperAxisExtremeArcClosure
import Markov.PaperAxisExtremeAdjacentArcs

/-! An actual primitive simple-period diagram cannot contain both adjacent
corner packets. Actual nearest-corner geometry and connectedness supply the
extremal diagram, its genuine incidences give four adjacent arcs, and the
original word/H1 parity contradiction excludes it. No peripheral free-class
identity or general class/H1 classifier is assumed. -/
noncomputable section
open Set
namespace Markov

private theorem adjacentSide_parity (x y : Fin 4)
    (h : y=x+1 ∨ x=y+1) : x.val%2 ≠ y.val%2 := by
  revert x y
  decide

/-- Positive actual 01 and 12 corner counts are impossible for primitive
original H1. The former explicit ARC-closure premise is genuinely discharged. -/
theorem paperAxisProperArcSixCount_corner_mul_eq_zero_of_primitive
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (hp : IsCoprime (paperTraceAbelianizationCoordinates g).toAdd.1
      (paperTraceAbelianizationCoordinates g).toAdd.2) :
    paperAxisProperArcSixCount g hg a ha 0 * paperAxisProperArcSixCount g hg a ha 1 = 0 := by
  by_cases h0 : paperAxisProperArcSixCount g hg a ha 0=0
  · simp only [h0,zero_mul]
  by_cases h1 : paperAxisProperArcSixCount g hg a ha 1=0
  · simp only [h1,mul_zero]
  have hp0 := Nat.pos_of_ne_zero h0
  have hp1 := Nat.pos_of_ne_zero h1
  have hS := paperAxisExtremeEndpointSet_eq_univ_of_corner_positive g hg a ha hproject hp0 hp1
  have hN := paperAxisPeriodCellWord_length_four_of_corner_positive_all_extreme
    g hg a ha hproject hS hp0 hp1
  have hc : ∀ i : paperAxisProperArcIndex g hg a,
      (paperAxisProperEndpointSide g hg a ha (i,0)).val%2 ≠
        (paperAxisProperEndpointSide g hg a ha (i,1)).val%2 := by
    intro i
    exact adjacentSide_parity _ _
      (paperAxisProperArc_adjacent_sides_of_corner_positive_all_extreme
        g hg a ha hproject hS hp0 hp1 i)
  exact (paperAxisPeriodCellWord_not_primitive_of_four_adjacent_arcs
    g hg a ha hproject hN hc hp).elim

/-- One of the two actual adjacent corner packets is empty for primitive
original H1. Opposite corner equalities and e*f=0 are separately checked. -/
theorem paperAxisProperArcSixCount_corner_zero_or_zero_of_primitive
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (hp : IsCoprime (paperTraceAbelianizationCoordinates g).toAdd.1
      (paperTraceAbelianizationCoordinates g).toAdd.2) :
    paperAxisProperArcSixCount g hg a ha 0=0 ∨ paperAxisProperArcSixCount g hg a ha 1=0 :=
  Nat.mul_eq_zero.mp (paperAxisProperArcSixCount_corner_mul_eq_zero_of_primitive
    g hg a ha hproject hp)

end Markov
