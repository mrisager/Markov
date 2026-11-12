import Markov.PaperAxisCellNoBacktrack

/-! Actual letters of the constructed ordered geodesic cell word satisfy the
literal neighboring-label ratio and have no immediate inverse pair. This uses
the actual no-return geometry, not an assumed reducedness field. -/
noncomputable section
open Set Topology
namespace Markov

/-- Actual gap labels extended to natural indices by clamping at the last gap. -/
def paperAxisPeriodCellLabelNat (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) (n : ℕ) : modularTraceSubgroup :=
  paperAxisPeriodGapCellLabel g hg a
    ⟨min n ((paperAxisPeriodCutPoints g hg a).card-2), by
      have := paperAxisPeriodCutPoints_two_le g hg a
      have := min_le_right n ((paperAxisPeriodCutPoints g hg a).card-2)
      omega⟩

private theorem wordReduced_nat_label_eq
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (n : ℕ) (hn : n < (paperAxisPeriodCutPoints g hg a).card-1) :
    paperAxisPeriodCellLabelNat g hg a n = paperAxisPeriodGapCellLabel g hg a ⟨n,hn⟩ := by
  unfold paperAxisPeriodCellLabelNat
  exact congrArg (paperAxisPeriodGapCellLabel g hg a) (Fin.ext (min_eq_left (by omega)))

private theorem wordReduced_neighbor_inv_letter (k : Fin 4) :
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
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩

private theorem wordReduced_ratio_letter
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (n : ℕ) (hn : n < (paperAxisPeriodCutPoints g hg a).card-2) :
    ∃ k : Fin 4, (paperAxisPeriodCellLabelNat g hg a n)⁻¹ *
      paperAxisPeriodCellLabelNat g hg a (n+1) = paperQuadrilateralSideNeighbor k := by
  have hN := paperAxisPeriodCutPoints_two_le g hg a
  let i : Fin ((paperAxisPeriodCutPoints g hg a).card-1) := ⟨n,by omega⟩
  let j : Fin ((paperAxisPeriodCutPoints g hg a).card-1) := ⟨n+1,by omega⟩
  have hi : paperAxisPeriodCellLabelNat g hg a n = paperAxisPeriodGapCellLabel g hg a i :=
    wordReduced_nat_label_eq g hg a n i.isLt
  have hj : paperAxisPeriodCellLabelNat g hg a (n+1) = paperAxisPeriodGapCellLabel g hg a j :=
    wordReduced_nat_label_eq g hg a (n+1) j.isLt
  obtain ⟨k,hstep⟩ := paperAxisPeriodGapCellLabel_adjacent_step g hg a i j rfl
  rcases hstep with he | he
  · refine ⟨k,?_⟩
    rw [hi,hj,he,← mul_assoc,inv_mul_cancel,one_mul]
  · obtain ⟨l,hl⟩ := wordReduced_neighbor_inv_letter k
    refine ⟨l,?_⟩
    rw [hi,hj,he,← mul_assoc,inv_mul_cancel,one_mul,hl]

/-- Each literal chosen word letter is its actual neighboring-cell ratio.
Unfolding the already constructed choice uses proof irrelevance; no new
letter choice, itinerary premise or action field is introduced. -/
theorem paperAxisPeriodCellWord_getElem_ratio
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (n : ℕ) (hn : n < (paperAxisPeriodCellWord g hg a).length) :
    paperQuadrilateralSideNeighbor ((paperAxisPeriodCellWord g hg a)[n]'hn) =
      (paperAxisPeriodCellLabelNat g hg a n)⁻¹ * paperAxisPeriodCellLabelNat g hg a (n+1) := by
  have hn' : n < (paperAxisPeriodCutPoints g hg a).card-2 := by
    simpa only [paperAxisPeriodCellWord_length] using hn
  unfold paperAxisPeriodCellWord
  rw [List.getElem_map,List.getElem_range]
  change paperQuadrilateralSideNeighbor
      (if h : n < (paperAxisPeriodCutPoints g hg a).card-2 then
        (wordReduced_ratio_letter g hg a n h).choose else 0) = _
  rw [dif_pos hn']
  exact (wordReduced_ratio_letter g hg a n hn').choose_spec.symm

/-- The ACTUAL ordered cell word of every hyperbolic axis has no immediate
inverse letters: two such letters would geometrically return across the same
supporting side, already ruled out by single intersection. -/
theorem paperAxisPeriodCellWord_no_immediate_inverse
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (n : ℕ) (hn : n+1 < (paperAxisPeriodCellWord g hg a).length) :
    paperQuadrilateralSideNeighbor ((paperAxisPeriodCellWord g hg a)[n]'(by omega)) *
      paperQuadrilateralSideNeighbor ((paperAxisPeriodCellWord g hg a)[n+1]'hn) ≠ 1 := by
  have hn' : n+1 < (paperAxisPeriodCutPoints g hg a).card-2 := by
    simpa only [paperAxisPeriodCellWord_length] using hn
  let i : Fin ((paperAxisPeriodCutPoints g hg a).card-1) := ⟨n,by omega⟩
  let j : Fin ((paperAxisPeriodCutPoints g hg a).card-1) := ⟨n+1,by omega⟩
  let k : Fin ((paperAxisPeriodCutPoints g hg a).card-1) := ⟨n+2,by omega⟩
  intro hback
  rw [paperAxisPeriodCellWord_getElem_ratio, paperAxisPeriodCellWord_getElem_ratio] at hback
  have he : paperAxisPeriodCellLabelNat g hg a n = paperAxisPeriodCellLabelNat g hg a (n+2) := by
    apply inv_mul_eq_one.mp
    simpa only [mul_assoc,mul_inv_cancel_left] using hback
  apply paperAxisPeriodGapCellLabel_ne_two_steps g hg a i j k rfl rfl
  have hi := wordReduced_nat_label_eq g hg a n i.isLt
  have hk := wordReduced_nat_label_eq g hg a (n+2) k.isLt
  exact hi.symm.trans (he.trans hk)

end Markov
