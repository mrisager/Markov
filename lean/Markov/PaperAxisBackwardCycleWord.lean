import Markov.PaperAxisSourceCycleWord
import Markov.PaperAxisProperEndpointOpposite
import Mathlib.Logic.Function.Iterate

/-! Literal backwards/role-one cell words. The actual predecessor source
labels are the opposite-label map of the reversed forward rotation, with its
one-step phase derived from actual endpoint gluing. No canonical reversal or
free-class classification is assumed. -/
noncomputable section
open Set
namespace Markov

/-- The literal opposite-side alphabet is the group inverse alphabet. -/
theorem paperQuadrilateralSideNeighbor_opposite_eq_inv (k : Fin 4) :
    paperQuadrilateralSideNeighbor (paperQuadrilateralOppositeSide k)=
      (paperQuadrilateralSideNeighbor k)⁻¹ := by
  fin_cases k
  · apply Subtype.ext
    change paperGeneratorASL=(paperGeneratorASL⁻¹)⁻¹
    exact (inv_inv _).symm
  · apply Subtype.ext
    change paperGeneratorBSL=(paperGeneratorBSL⁻¹)⁻¹
    exact (inv_inv _).symm
  · rfl
  · rfl

/-- Actual source i is glued to the preceding target, so it has the literal
opposite side of target Prev(i). This fixes the backwards one-step phase. -/
theorem paperAxisSourceSide_eq_opposite_prevTarget
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (i : paperAxisProperArcIndex g hg a) :
    paperAxisProperEndpointSide g hg a ha (i,0)=
      paperQuadrilateralOppositeSide (paperAxisProperEndpointSide g hg a ha
        (paperAxisProperArcPrevIndex g hg a i,1)) := by
  simpa only [paperAxisProperArcNextIndex_prev] using
    (paperAxisProperEndpoint_cyclic_gluing_opposite_and_coordinate
      g hg a ha hproject (paperAxisProperArcPrevIndex g hg a i)).1

private theorem next_full_period
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (i : paperAxisProperArcIndex g hg a) :
    ((paperAxisProperArcNextIndex g hg a)^[(paperAxisPeriodCutPoints g hg a).card-2]) i=i := by
  apply Fin.ext
  rw [paperAxisProperArcNextIndex_iterate_val]
  simpa only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod] using
    Nat.mod_eq_of_lt i.isLt

private theorem prev_iterate_eq_next_complement
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (i : paperAxisProperArcIndex g hg a) (m : ℕ)
    (hm : m≤(paperAxisPeriodCutPoints g hg a).card-2) :
    ((paperAxisProperArcPrevIndex g hg a)^[m]) i=
      ((paperAxisProperArcNextIndex g hg a)^[(paperAxisPeriodCutPoints g hg a).card-2-m]) i := by
  have hl : Function.LeftInverse (paperAxisProperArcPrevIndex g hg a)
      (paperAxisProperArcNextIndex g hg a) := paperAxisProperArcPrevIndex_next g hg a
  have hr : Function.LeftInverse (paperAxisProperArcNextIndex g hg a)
      (paperAxisProperArcPrevIndex g hg a) := paperAxisProperArcNextIndex_prev g hg a
  apply (hl.iterate m).injective
  rw [(hr.iterate m) i, ← Function.iterate_add_apply, Nat.add_sub_of_le hm]
  exact (next_full_period g hg a i).symm

/-- Reading actual sources along Prev is exactly the opposite-label map of
REVERSE of the forward rotation starting at i. The first letter is therefore
Opp(Target Prev(i)), not Opp(Target i). -/
theorem paperAxisPrevSourceCycle_eq_reverse_rotate
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (i : paperAxisProperArcIndex g hg a) :
    List.ofFn (fun j : paperAxisProperArcIndex g hg a =>
      paperAxisProperEndpointSide g hg a ha
        (((paperAxisProperArcPrevIndex g hg a)^[j.val]) i,0)) =
      ((paperAxisPeriodCellWord g hg a).rotate i.val).reverse.map paperQuadrilateralOppositeSide := by
  rw [paperAxisPeriodCellWord_rotate_eq_sourceCycle g hg a ha i]
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_map,List.length_reverse]
  · intro n hn hm
    have hn' : n<(paperAxisPeriodCutPoints g hg a).card-2 := by
      simpa only [List.length_ofFn] using hn
    rw [List.getElem_ofFn,List.getElem_map,List.getElem_reverse,List.getElem_ofFn]
    simp only [List.length_ofFn]
    rw [paperAxisSourceSide_eq_opposite_prevTarget g hg a ha hproject]
    congr 2
    rw [← Function.iterate_succ_apply' (paperAxisProperArcPrevIndex g hg a) n i]
    have he := prev_iterate_eq_next_complement g hg a i (n+1) (by omega)
    have hsub : (paperAxisPeriodCutPoints g hg a).card-2-(n+1) =
        (paperAxisPeriodCutPoints g hg a).card-2-1-n := by omega
    rw [hsub] at he
    exact congrArg (fun j : paperAxisProperArcIndex g hg a => (j,(1:Fin 2))) he

/-- Equivalently, this is a rotation of the reversed actual word, with the
EXACT phase length-i. Reversal has not been identified with a canonical rotation. -/
theorem paperAxisPrevSourceCycle_eq_rotate_reverse
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (i : paperAxisProperArcIndex g hg a) :
    List.ofFn (fun j : paperAxisProperArcIndex g hg a =>
      paperAxisProperEndpointSide g hg a ha
        (((paperAxisProperArcPrevIndex g hg a)^[j.val]) i,0)) =
      ((paperAxisPeriodCellWord g hg a).reverse.rotate
        ((paperAxisPeriodCellWord g hg a).length-i.val)).map paperQuadrilateralOppositeSide := by
  rw [paperAxisPrevSourceCycle_eq_reverse_rotate g hg a ha hproject i,List.reverse_rotate]
  have hi : i.val<(paperAxisPeriodCellWord g hg a).length := by
    simpa only [paperAxisPeriodCellWord_length] using i.isLt
  rw [Nat.mod_eq_of_lt hi]

private theorem opposite_reverse_prod (w : List (Fin 4)) :
    ((w.reverse.map paperQuadrilateralOppositeSide).map paperQuadrilateralSideNeighbor).prod=
      (w.map paperQuadrilateralSideNeighbor).prod⁻¹ := by
  induction w with
  | nil => simp
  | cons k w ih =>
      simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
        List.prod_append,List.prod_cons,List.prod_nil,mul_one,
        paperQuadrilateralSideNeighbor_opposite_eq_inv,ih,mul_inv_rev]

private theorem backward_rotate_prod {G : Type*} [Group G] (w : List G) (r : ℕ) :
    (w.rotate r).prod=(w.take (r%w.length)).prod⁻¹*w.prod*(w.take (r%w.length)).prod := by
  rw [List.rotate_eq_drop_append_take_mod,List.prod_append]
  have hs : w.prod=(w.take (r%w.length)).prod*(w.drop (r%w.length)).prod := by
    rw [← List.prod_append,List.take_append_drop]
  rw [hs]
  simp only [inv_mul_cancel_left]

/-- The literal backwards neighbor product is an INVERSE conjugate of the
actual word product, with its explicit length-i phase and actual prefix. -/
theorem paperAxisPrevSourceCycle_neighbor_prod
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (i : paperAxisProperArcIndex g hg a) :
    ((List.ofFn (fun j : paperAxisProperArcIndex g hg a =>
      paperAxisProperEndpointSide g hg a ha
        (((paperAxisProperArcPrevIndex g hg a)^[j.val]) i,0))).map paperQuadrilateralSideNeighbor).prod =
      (((paperAxisPeriodCellWord g hg a).take i.val).map paperQuadrilateralSideNeighbor).prod⁻¹ *
        ((paperAxisPeriodCellWord g hg a).map paperQuadrilateralSideNeighbor).prod⁻¹ *
      (((paperAxisPeriodCellWord g hg a).take i.val).map paperQuadrilateralSideNeighbor).prod := by
  rw [paperAxisPrevSourceCycle_eq_reverse_rotate g hg a ha hproject i,opposite_reverse_prod]
  have h := backward_rotate_prod ((paperAxisPeriodCellWord g hg a).map paperQuadrilateralSideNeighbor) i.val
  rw [← List.map_rotate] at h
  simp only [List.length_map,← List.map_take] at h
  have hi : i.val<(paperAxisPeriodCellWord g hg a).length := by
    simpa only [paperAxisPeriodCellWord_length] using i.isLt
  rw [Nat.mod_eq_of_lt hi] at h
  rw [h]
  simp only [mul_inv_rev,inv_inv,mul_assoc]

end Markov
