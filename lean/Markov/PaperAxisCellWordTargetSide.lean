import Markov.PaperAxisCellWordReduced
import Markov.PaperAxisProperEndpointTags
import Mathlib.Data.List.OfFn

/-! The literal constructed cell word is the target-side sequence of the
actual proper-Q arc family. This attaches the actual endpoint diagram to the
already constructed word; no side-word, simplicity or classification premise
is supplied. -/

noncomputable section
open Set
namespace Markov

private theorem targetWord_label_eq
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (n : ℕ) (hn : n < (paperAxisPeriodCutPoints g hg a).card - 1) :
    paperAxisPeriodCellLabelNat g hg a n =
      paperAxisPeriodGapCellLabel g hg a ⟨n, hn⟩ := by
  unfold paperAxisPeriodCellLabelNat
  exact congrArg (paperAxisPeriodGapCellLabel g hg a)
    (Fin.ext (min_eq_left (by omega)))

private theorem targetWord_arc_label
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (i : paperAxisProperArcIndex g hg a) :
    paperAxisProperArcCellLabel g hg a i = paperAxisPeriodCellLabelNat g hg a i.val := by
  have hi := i.isLt
  rw [targetWord_label_eq g hg a i.val (by omega)]
  by_cases hzero : i.val = 0
  · simp only [paperAxisProperArcCellLabel, if_pos hzero]
    congr 1
    apply Fin.ext
    exact hzero.symm
  · simp only [paperAxisProperArcCellLabel, if_neg hzero]
    rfl

private theorem targetWord_parameter_one
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (i : paperAxisProperArcIndex g hg a) :
    paperAxisProperArcParameter g hg a i 1 =
      paperAxisPeriodCutTable g hg a ⟨i.val + 1, by have := i.isLt; omega⟩ := by
  by_cases hi : i.val = 0
  · simp only [paperAxisProperArcParameter, if_pos hi,
      show ((1 : unitInterval) : ℝ) = 1 from rfl, mul_one, add_sub_cancel,
      paperAxisWrapRightTime]
    congr 1
    apply Fin.ext
    change 0 + 1 = i.val + 1
    omega
  · simp only [paperAxisProperArcParameter, if_neg hi, paperAxisPeriodGapParameter,
      show ((1 : unitInterval) : ℝ) = 1 from rfl, mul_one, add_sub_cancel]
    rfl

/-- Each actual word letter is exactly the actual original side of the
corresponding proper arc's target. The wrap member is index zero, whose
target is the first internal table cut. No embeddedness premise is needed. -/
theorem paperAxisPeriodCellWord_getElem_eq_targetSide
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (i : paperAxisProperArcIndex g hg a) :
    (paperAxisPeriodCellWord g hg a)[i.val]'(by
      rw [paperAxisPeriodCellWord_length]; exact i.isLt) =
      paperAxisProperEndpointSide g hg a ha (i, 1) := by
  have hi := i.isLt
  let j : Fin ((paperAxisPeriodCutPoints g hg a).card - 1) := ⟨i.val, by omega⟩
  let j' : Fin ((paperAxisPeriodCutPoints g hg a).card - 1) := ⟨i.val + 1, by omega⟩
  let k : Fin 4 := (paperAxisPeriodCellWord g hg a)[i.val]'(by
    rw [paperAxisPeriodCellWord_length]; exact i.isLt)
  let z := paperAxisProperEndpointPoint g hg a ha (i, 1)
  have hratio : paperQuadrilateralSideNeighbor k =
      (paperAxisProperArcCellLabel g hg a i)⁻¹ * paperAxisPeriodGapCellLabel g hg a j' := by
    rw [targetWord_arc_label]
    exact (paperAxisPeriodCellWord_getElem_ratio g hg a i.val _).trans
      (congrArg (fun x => (paperAxisPeriodCellLabelNat g hg a i.val)⁻¹ * x)
        (targetWord_label_eq g hg a (i.val + 1) j'.isLt))
  have hsmul : paperAxisProperArcCellLabel g hg a i • (z : UpperHalfPlane) =
      modularHyperbolicAxis g hg
        (paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a j)) := by
    have hs := paperAxisProperArc_smul g hg a ha i 1
    rw [targetWord_parameter_one] at hs
    exact hs
  have hnext := (paperAxisPeriodGapCut_mem_both_label_cells g hg a j j' rfl).2
  obtain ⟨w, hw, hweq⟩ := hnext
  change paperAxisPeriodGapCellLabel g hg a j' • w = _ at hweq
  have hside : (z : UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide k := by
    rw [← paperQuadrilateral_neighbor_intersection_eq_side]
    refine ⟨z.property, w, hw, ?_⟩
    apply (modularTraceSubgroup_isometry (paperAxisProperArcCellLabel g hg a i)).injective
    change paperAxisProperArcCellLabel g hg a i • (paperQuadrilateralSideNeighbor k • w) =
      paperAxisProperArcCellLabel g hg a i • (z : UpperHalfPlane)
    rw [← mul_smul, hratio, mul_inv_cancel_left]
    exact hweq.trans hsmul.symm
  exact paperAxisProperEndpointSide_unique g hg a ha (i, 1) k hside

/-- The entire actual ordered side word is the literal target-side list of
the actual proper-Q family, including its joined wrap member. -/
theorem paperAxisPeriodCellWord_eq_targetSide_list
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) :
    paperAxisPeriodCellWord g hg a =
      List.ofFn (fun i : paperAxisProperArcIndex g hg a =>
        paperAxisProperEndpointSide g hg a ha (i, 1)) := by
  apply List.ext_getElem
  · simp only [paperAxisPeriodCellWord_length, List.length_ofFn]
  · intro n hn hm
    have hn' : n < (paperAxisPeriodCutPoints g hg a).card - 2 := by
      simpa only [paperAxisPeriodCellWord_length] using hn
    simpa only [List.getElem_ofFn] using
      paperAxisPeriodCellWord_getElem_eq_targetSide g hg a ha ⟨n, hn'⟩

end Markov
