import Markov.PaperAxisCyclicCellLabels
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! A literal finite ordered original-side alphabet word is constructed from
actual neighboring cell labels. Its noncommutative List product is the actual
period deck element conjugated by the actual first cell label. -/
noncomputable section
open Set Topology
namespace Markov

private theorem orderedCellNeighbor_inv_letter (k : Fin 4) :
    ∃ l : Fin 4, (paperQuadrilateralSideNeighbor k)⁻¹ = paperQuadrilateralSideNeighbor l := by
  fin_cases k
  · refine ⟨2, ?_⟩
    apply Subtype.ext
    change (paperGeneratorASL⁻¹)⁻¹ = paperGeneratorASL
    exact inv_inv _
  · refine ⟨3, ?_⟩
    apply Subtype.ext
    change (paperGeneratorBSL⁻¹)⁻¹ = paperGeneratorBSL
    exact inv_inv _
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

private def orderedCellLabelNat (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) (n : ℕ) : modularTraceSubgroup :=
  paperAxisPeriodGapCellLabel g hg a
    ⟨min n ((paperAxisPeriodCutPoints g hg a).card-2), by
      have := paperAxisPeriodCutPoints_two_le g hg a
      have := min_le_right n ((paperAxisPeriodCutPoints g hg a).card-2)
      omega⟩

private theorem orderedCellRatio_letter
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (n : ℕ) (hn : n < (paperAxisPeriodCutPoints g hg a).card-2) :
    ∃ k : Fin 4, (orderedCellLabelNat g hg a n)⁻¹ * orderedCellLabelNat g hg a (n+1) =
      paperQuadrilateralSideNeighbor k := by
  have hN := paperAxisPeriodCutPoints_two_le g hg a
  let i : Fin ((paperAxisPeriodCutPoints g hg a).card-1) := ⟨n, by omega⟩
  let j : Fin ((paperAxisPeriodCutPoints g hg a).card-1) := ⟨n+1, by omega⟩
  have hi : orderedCellLabelNat g hg a n = paperAxisPeriodGapCellLabel g hg a i := by
    unfold orderedCellLabelNat
    congr 1
    apply Fin.ext
    exact min_eq_left (by omega)
  have hj : orderedCellLabelNat g hg a (n+1) = paperAxisPeriodGapCellLabel g hg a j := by
    unfold orderedCellLabelNat
    congr 1
    apply Fin.ext
    exact min_eq_left (by omega)
  obtain ⟨k, hstep⟩ := paperAxisPeriodGapCellLabel_adjacent_step g hg a i j rfl
  rcases hstep with he | he
  · refine ⟨k, ?_⟩
    rw [hi, hj, he, ← mul_assoc, inv_mul_cancel, one_mul]
  · obtain ⟨l, hl⟩ := orderedCellNeighbor_inv_letter k
    refine ⟨l, ?_⟩
    rw [hi, hj, he, ← mul_assoc, inv_mul_cancel, one_mul, hl]

private def orderedCellLetter (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) (n : ℕ) : Fin 4 :=
  if hn : n < (paperAxisPeriodCutPoints g hg a).card-2 then
    (orderedCellRatio_letter g hg a n hn).choose else 0

private theorem orderedCellLetter_spec
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (n : ℕ) (hn : n < (paperAxisPeriodCutPoints g hg a).card-2) :
    (orderedCellLabelNat g hg a n)⁻¹ * orderedCellLabelNat g hg a (n+1) =
      paperQuadrilateralSideNeighbor (orderedCellLetter g hg a n) := by
  unfold orderedCellLetter
  rw [dif_pos hn]
  exact (orderedCellRatio_letter g hg a n hn).choose_spec

/-- Actual ordered side letters, each indexing the literal alphabet
[A^-1,B^-1,A,B]. The letters are chosen from the proved actual adjacent ratios. -/
def paperAxisPeriodCellWord (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) : List (Fin 4) :=
  (List.range ((paperAxisPeriodCutPoints g hg a).card-2)).map (orderedCellLetter g hg a)

/-- The actual word has one letter for each step between consecutive gap labels. -/
theorem paperAxisPeriodCellWord_length
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    (paperAxisPeriodCellWord g hg a).length = (paperAxisPeriodCutPoints g hg a).card-2 := by
  simp only [paperAxisPeriodCellWord, List.length_map, List.length_range]

/-- The literal ordered noncommutative product reconstructs the actual deck
period, conjugated by the actual first cell label. No word-product premise,
abelianization or arbitrary simple-class classification is used. -/
theorem paperAxisPeriodCellWord_prod
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) :
    ((paperAxisPeriodCellWord g hg a).map paperQuadrilateralSideNeighbor).prod =
      (paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a))⁻¹ *
        g * paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a) := by
  have heval : (paperAxisPeriodCellWord g hg a).map paperQuadrilateralSideNeighbor =
      (List.range ((paperAxisPeriodCutPoints g hg a).card-2)).map
        (fun n => (orderedCellLabelNat g hg a n)⁻¹ * orderedCellLabelNat g hg a (n+1)) := by
    rw [paperAxisPeriodCellWord, List.map_map]
    apply List.map_congr_left
    intro n hn
    exact (orderedCellLetter_spec g hg a n (List.mem_range.mp hn)).symm
  have hprod := List.prod_range_div' ((paperAxisPeriodCutPoints g hg a).card-2)
    (fun n => (orderedCellLabelNat g hg a n)⁻¹)
  simp only [div_eq_mul_inv, inv_inv] at hprod
  have hfirst : orderedCellLabelNat g hg a 0 =
      paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a) := by
    rfl
  have hlast : orderedCellLabelNat g hg a ((paperAxisPeriodCutPoints g hg a).card-2) =
      paperAxisPeriodGapCellLabel g hg a (paperAxisLastGapIndex g hg a) := by
    unfold orderedCellLabelNat paperAxisLastGapIndex
    exact congrArg (paperAxisPeriodGapCellLabel g hg a) (Fin.ext (min_self _))
  rw [heval, hprod, hfirst, hlast, paperAxisPeriodGapCellLabel_last_eq_period_mul_first g hg a ha,
    mul_assoc]

end Markov
