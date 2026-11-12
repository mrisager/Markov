import Markov.PaperAxisCellWordTargetSide
import Markov.PaperAxisCellWordH1
import Markov.PaperAxisProperEndpointOpposite
import Mathlib.RingTheory.Coprime.Basic

/-! Four actual adjacent-side arcs have nonprimitive original H1. The
geometric side/word/gluing dictionary supplies the parity alternation; no
free-class classification or peripheral-word identity is assumed. -/
noncomputable section
open Set
namespace Markov

private theorem oppositeSide_parity (k : Fin 4) :
    (paperQuadrilateralOppositeSide k).val % 2 = k.val % 2 := by
  fin_cases k <;> rfl

private theorem fourLetters_even (a b c d : Fin 4)
    (hab : a.val % 2 ≠ b.val % 2) (hbc : b.val % 2 ≠ c.val % 2)
    (hcd : c.val % 2 ≠ d.val % 2) :
    (2 : ℤ) ∣ (paperAxisCellLetterCoordinates a + paperAxisCellLetterCoordinates b +
      paperAxisCellLetterCoordinates c + paperAxisCellLetterCoordinates d).1 ∧
    (2 : ℤ) ∣ (paperAxisCellLetterCoordinates a + paperAxisCellLetterCoordinates b +
      paperAxisCellLetterCoordinates c + paperAxisCellLetterCoordinates d).2 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [paperAxisCellLetterCoordinates] at *

/-- The actual target-side letters alternate parity whenever every actual
arc joins adjacent side parities. Opposite-edge gluing preserves parity. -/
theorem paperAxisPeriodCellWord_target_parity_step
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (hcorner : ∀ i : paperAxisProperArcIndex g hg a,
      (paperAxisProperEndpointSide g hg a ha (i,0)).val % 2 ≠
        (paperAxisProperEndpointSide g hg a ha (i,1)).val % 2)
    (i : paperAxisProperArcIndex g hg a) :
    (paperAxisProperEndpointSide g hg a ha (i,1)).val % 2 ≠
      (paperAxisProperEndpointSide g hg a ha (paperAxisProperArcNextIndex g hg a i,1)).val % 2 := by
  have he := congrArg (fun k : Fin 4 => k.val % 2)
    (paperAxisProperEndpoint_cyclic_gluing_opposite_and_coordinate g hg a ha hproject i).1
  change (paperAxisProperEndpointSide g hg a ha (paperAxisProperArcNextIndex g hg a i,0)).val % 2 =
    (paperQuadrilateralOppositeSide (paperAxisProperEndpointSide g hg a ha (i,1))).val % 2 at he
  rw [oppositeSide_parity] at he
  exact fun h => hcorner (paperAxisProperArcNextIndex g hg a i) (he.trans h)

/-- Four actual adjacent-side proper arcs force BOTH original H1 coordinates
to be even. The length and side conditions are explicit actual diagram facts. -/
theorem paperAxisPeriodCellWord_even_coordinates_of_four_adjacent_arcs
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (hN : (paperAxisPeriodCellWord g hg a).length = 4)
    (hcorner : ∀ i : paperAxisProperArcIndex g hg a,
      (paperAxisProperEndpointSide g hg a ha (i,0)).val % 2 ≠
        (paperAxisProperEndpointSide g hg a ha (i,1)).val % 2) :
    (2 : ℤ) ∣ (paperTraceAbelianizationCoordinates g).toAdd.1 ∧
      (2 : ℤ) ∣ (paperTraceAbelianizationCoordinates g).toAdd.2 := by
  have hn : (paperAxisPeriodCutPoints g hg a).card-2 = 4 := by
    simpa only [paperAxisPeriodCellWord_length] using hN
  let ix (n : Fin 4) : paperAxisProperArcIndex g hg a :=
    ⟨n.val,by rw [hn]; exact n.isLt⟩
  let t (n : Fin 4) : Fin 4 := paperAxisProperEndpointSide g hg a ha (ix n,1)
  have hnext (i j : Fin 4) (hij : i.val+1=j.val) :
      paperAxisProperArcNextIndex g hg a (ix i) = ix j := by
    have hlt : (ix i).val+1 < (paperAxisPeriodCutPoints g hg a).card-2 := by
      change i.val+1 < _
      rw [hn,hij]
      exact j.isLt
    apply Fin.ext
    simp only [paperAxisProperArcNextIndex, dif_pos hlt]
    exact hij
  have hp (i j : Fin 4) (hij : i.val+1=j.val) : (t i).val%2 ≠ (t j).val%2 := by
    have h := paperAxisPeriodCellWord_target_parity_step g hg a ha hproject hcorner (ix i)
    rw [hnext i j hij] at h
    exact h
  have hw : paperAxisPeriodCellWord g hg a = [t 0,t 1,t 2,t 3] := by
    apply List.ext_getElem
    · simpa using hN
    · intro n hleft hright
      have hn4 : n<4 := by simpa only [List.length_cons,List.length_nil] using hright
      have hx := paperAxisPeriodCellWord_getElem_eq_targetSide g hg a ha
        ⟨n,by simpa only [paperAxisPeriodCellWord_length] using hleft⟩
      interval_cases n <;>
        simpa only [List.getElem_cons_zero,List.getElem_cons_succ] using hx
  have he := fourLetters_even (t 0) (t 1) (t 2) (t 3)
    (hp 0 1 rfl) (hp 1 2 rfl) (hp 2 3 rfl)
  have hsum : (2 : ℤ) ∣ ((paperAxisPeriodCellWord g hg a).map paperAxisCellLetterCoordinates).sum.1 ∧
      (2 : ℤ) ∣ ((paperAxisPeriodCellWord g hg a).map paperAxisCellLetterCoordinates).sum.2 := by
    simpa only [hw,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,add_assoc] using he
  simpa only [paperAxisPeriodCellWord_signedSum g hg a ha] using hsum

/-- This actual four-adjacent-arc configuration cannot have primitive
original H1. No nonabelian class is inferred from H1 in this contradiction. -/
theorem paperAxisPeriodCellWord_not_primitive_of_four_adjacent_arcs
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (hN : (paperAxisPeriodCellWord g hg a).length = 4)
    (hcorner : ∀ i : paperAxisProperArcIndex g hg a,
      (paperAxisProperEndpointSide g hg a ha (i,0)).val % 2 ≠
        (paperAxisProperEndpointSide g hg a ha (i,1)).val % 2) :
    ¬ IsCoprime (paperTraceAbelianizationCoordinates g).toAdd.1
      (paperTraceAbelianizationCoordinates g).toAdd.2 := by
  intro hp
  have he := paperAxisPeriodCellWord_even_coordinates_of_four_adjacent_arcs
    g hg a ha hproject hN hcorner
  have hu : IsUnit (2 : ℤ) := hp.isUnit_of_dvd' he.1 he.2
  norm_num [Int.isUnit_iff] at hu

end Markov
