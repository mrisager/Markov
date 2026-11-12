import Markov.PaperAxisCellWordTargetSide
import Markov.PaperAxisProperEndpointPairings
import Mathlib.Data.List.Rotate

/-! The actual proper-family successor, with its joined wrap member, gives
the literal cyclic order of the constructed original-side word. No geometric
normal form, itinerary equality, or preferred orientation is an input. -/

noncomputable section
open Set
namespace Markov

/-- The actual successor is addition of one modulo the actual family size. -/
theorem paperAxisProperArcNextIndex_val_mod
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (i : paperAxisProperArcIndex g hg a) :
    (paperAxisProperArcNextIndex g hg a i).val =
      (i.val + 1) % ((paperAxisPeriodCutPoints g hg a).card - 2) := by
  have hi := i.isLt
  by_cases hn : i.val + 1 < (paperAxisPeriodCutPoints g hg a).card - 2
  · simp only [paperAxisProperArcNextIndex, dif_pos hn]
    exact (Nat.mod_eq_of_lt hn).symm
  · simp only [paperAxisProperArcNextIndex, dif_neg hn]
    have he : i.val + 1 = (paperAxisPeriodCutPoints g hg a).card - 2 := by omega
    rw [he, Nat.mod_self]

/-- Every actual cyclic iterate has its literal modular index. -/
theorem paperAxisProperArcNextIndex_iterate_val
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (i : paperAxisProperArcIndex g hg a) (j : ℕ) :
    ((paperAxisProperArcNextIndex g hg a)^[j] i).val =
      (i.val + j) % ((paperAxisPeriodCutPoints g hg a).card - 2) := by
  induction j with
  | zero =>
      simpa only [Function.iterate_zero_apply, Nat.add_zero] using
        (Nat.mod_eq_of_lt i.isLt).symm
  | succ j ih =>
      rw [Function.iterate_succ_apply', paperAxisProperArcNextIndex_val_mod, ih,
        Nat.mod_add_mod]
      congr 1

/-- Rotating the ACTUAL constructed side word is exactly reading target
labels along the ACTUAL successor cycle. This includes the wrap member. -/
theorem paperAxisPeriodCellWord_rotate_eq_sourceCycle
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (i : paperAxisProperArcIndex g hg a) :
    (paperAxisPeriodCellWord g hg a).rotate i.val =
      List.ofFn (fun j : paperAxisProperArcIndex g hg a =>
        paperAxisProperEndpointSide g hg a ha
          (((paperAxisProperArcNextIndex g hg a)^[j.val]) i, 1)) := by
  apply List.ext_getElem
  · simp only [List.length_rotate, paperAxisPeriodCellWord_length, List.length_ofFn]
  · intro n hn hm
    have hN : 0 < (paperAxisPeriodCutPoints g hg a).card - 2 :=
      lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hn' : n < (paperAxisPeriodCutPoints g hg a).card - 2 := by
      simpa only [List.length_ofFn] using hm
    rw [List.getElem_rotate, List.getElem_ofFn]
    simp only [paperAxisPeriodCellWord_length]
    let k : paperAxisProperArcIndex g hg a :=
      ⟨(n + i.val) % ((paperAxisPeriodCutPoints g hg a).card - 2), Nat.mod_lt _ hN⟩
    have he : k = ((paperAxisProperArcNextIndex g hg a)^[n]) i := by
      apply Fin.ext
      rw [paperAxisProperArcNextIndex_iterate_val]
      exact congrArg (fun x => x % ((paperAxisPeriodCutPoints g hg a).card - 2))
        (Nat.add_comm n i.val)
    exact (paperAxisPeriodCellWord_getElem_eq_targetSide g hg a ha k).trans
      (congrArg (fun t => paperAxisProperEndpointSide g hg a ha (t, 1)) he)

end Markov
