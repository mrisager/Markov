import Markov.PaperAxisCellWordReduced

/-! The actual side word of a hyperbolic axis is cyclically nonbacktracking.
The wrap case is proved from the actual joined wrap arc and literal period
cell labels. No embeddedness or simple-class classification premise is used. -/
noncomputable section
open Set Topology
namespace Markov

private theorem cyclicReduced_nat_label_eq
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (n : ℕ) (hn : n < (paperAxisPeriodCutPoints g hg a).card-1) :
    paperAxisPeriodCellLabelNat g hg a n = paperAxisPeriodGapCellLabel g hg a ⟨n,hn⟩ := by
  unfold paperAxisPeriodCellLabelNat
  exact congrArg (paperAxisPeriodGapCellLabel g hg a) (Fin.ext (min_eq_left (by omega)))

private theorem cyclicReduced_pair_subsingleton
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (δ ε : modularTraceSubgroup)
    (hstep : ∃ k : Fin 4, ε = δ * paperQuadrilateralSideNeighbor k ∨
      ε = δ * (paperQuadrilateralSideNeighbor k)⁻¹) :
    {t : ℝ | modularHyperbolicAxis g hg t ∈
        (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral ∧
      modularHyperbolicAxis g hg t ∈
        (fun z : UpperHalfPlane => ε • z) '' paperIdealQuadrilateral}.Subsingleton := by
  obtain ⟨k,hk⟩ := hstep
  rcases hk with hk | hk
  · rw [hk]
    exact modularHyperbolicAxis_neighbor_cell_intersection_subsingleton g hg δ k
  · have hd : δ = ε * paperQuadrilateralSideNeighbor k := by
      rw [hk,mul_assoc,inv_mul_cancel,mul_one]
    intro s hs t ht
    apply modularHyperbolicAxis_neighbor_cell_intersection_subsingleton g hg ε k
    · exact ⟨hs.2,hd ▸ hs.1⟩
    · exact ⟨ht.2,hd ▸ ht.1⟩

/-- Genuine off-cut period bases yield a nonempty ACTUAL side word. -/
theorem paperAxisPeriodCellWord_length_pos_of_off_sides
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) :
    0 < (paperAxisPeriodCellWord g hg a).length := by
  rw [paperAxisPeriodCellWord_length]
  have := paperAxisPeriodCutPoints_three_le_of_off_sides g hg a ha
  omega

/-- Actual cyclic labels cannot backtrack at the chosen period seam. Such a
backtrack would put BOTH distinct wrap cuts in the same actual neighboring
cell pair and hence on one fixed translated supporting geodesic. -/
theorem paperAxisPeriodCellLabelNat_wrap_no_backtrack
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) :
    paperAxisPeriodCellLabelNat g hg a ((paperAxisPeriodCutPoints g hg a).card-3) ≠
      g * paperAxisPeriodCellLabelNat g hg a 1 := by
  have hN := paperAxisPeriodCutPoints_three_le_of_off_sides g hg a ha
  let first := paperAxisFirstGapIndex g hg a
  let second : Fin ((paperAxisPeriodCutPoints g hg a).card-1) := ⟨1,by omega⟩
  let beforeLast : Fin ((paperAxisPeriodCutPoints g hg a).card-1) :=
    ⟨(paperAxisPeriodCutPoints g hg a).card-3,by omega⟩
  intro hback
  have hlabels : paperAxisPeriodGapCellLabel g hg a beforeLast =
      g * paperAxisPeriodGapCellLabel g hg a second := by
    have hb := cyclicReduced_nat_label_eq g hg a beforeLast.val beforeLast.isLt
    have hs := cyclicReduced_nat_label_eq g hg a second.val second.isLt
    exact hb.symm.trans (hback.trans (congrArg (fun x : modularTraceSubgroup => g*x) hs))
  have hleftFirst : modularHyperbolicAxis g hg (paperAxisWrapLeftTime g hg a) ∈
      (fun z : UpperHalfPlane => paperAxisPeriodGapCellLabel g hg a first • z) ''
        paperIdealQuadrilateral :=
    (paperAxisWrapInterval_cell g hg a ha).1 _
      ⟨le_rfl,(lt_trans (paperAxisWrapTimes_straddle g hg a).1
        (paperAxisWrapTimes_straddle g hg a).2).le⟩
  have hrightFirst : modularHyperbolicAxis g hg (paperAxisWrapRightTime g hg a) ∈
      (fun z : UpperHalfPlane => paperAxisPeriodGapCellLabel g hg a first • z) ''
        paperIdealQuadrilateral :=
    (paperAxisWrapInterval_cell g hg a ha).1 _
      ⟨(lt_trans (paperAxisWrapTimes_straddle g hg a).1
        (paperAxisWrapTimes_straddle g hg a).2).le,le_rfl⟩
  have hsecondLeft : paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a second) =
      paperAxisWrapRightTime g hg a := rfl
  have hrightSecond : modularHyperbolicAxis g hg (paperAxisWrapRightTime g hg a) ∈
      (fun z : UpperHalfPlane => paperAxisPeriodGapCellLabel g hg a second • z) ''
        paperIdealQuadrilateral := by
    apply (paperAxisPeriodGapCellLabel_spec g hg a second).2
    rw [← hsecondLeft]
    exact ⟨le_rfl,(nonempty_Ioo.mp (paperAxisPeriodCutTable_gap_nonempty g hg a
      (paperAxisGapLeftIndex g hg a second) (paperAxisGapRightIndex g hg a second) rfl)).le⟩
  have htime : paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a beforeLast) =
      paperAxisWrapLeftTime g hg a+modularClosedGeodesicPeriod g := by
    dsimp only [paperAxisWrapLeftTime]
    rw [sub_add_cancel]
    congr 1
    apply Fin.ext
    change (paperAxisPeriodCutPoints g hg a).card-3+1 =
      (paperAxisPeriodCutPoints g hg a).card-2
    omega
  have hleftSecond : modularHyperbolicAxis g hg (paperAxisWrapLeftTime g hg a) ∈
      (fun z : UpperHalfPlane => paperAxisPeriodGapCellLabel g hg a second • z) ''
        paperIdealQuadrilateral := by
    have hmem := (paperAxisPeriodGapCellLabel_spec g hg a beforeLast).2
      (paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a beforeLast))
      ⟨(nonempty_Ioo.mp (paperAxisPeriodCutTable_gap_nonempty g hg a
        (paperAxisGapLeftIndex g hg a beforeLast) (paperAxisGapRightIndex g hg a beforeLast) rfl)).le,
        le_rfl⟩
    obtain ⟨z,hz,heq⟩ := hmem
    change paperAxisPeriodGapCellLabel g hg a beforeLast • z = _ at heq
    rw [hlabels,htime,mul_smul,← modularHyperbolicAxis_action] at heq
    exact ⟨z,hz,(modularTraceSubgroup_isometry g).injective heq⟩
  have hpair := cyclicReduced_pair_subsingleton g hg
    (paperAxisPeriodGapCellLabel g hg a first) (paperAxisPeriodGapCellLabel g hg a second)
    (paperAxisPeriodGapCellLabel_adjacent_step g hg a first second rfl)
  have heq := hpair ⟨hleftFirst,hleftSecond⟩ ⟨hrightFirst,hrightSecond⟩
  exact (lt_trans (paperAxisWrapTimes_straddle g hg a).1
    (paperAxisWrapTimes_straddle g hg a).2).ne heq

/-- EVERY cyclically adjacent pair of ACTUAL word letters is noninverse,
including the last/first pair. Cyclic adjacency is the literal modulo index
relation on the nonempty constructed finite word, not a reducedness field. -/
theorem paperAxisPeriodCellWord_no_cyclic_inverse
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (i j : Fin (paperAxisPeriodCellWord g hg a).length)
    (hnext : j.val = (i.val+1) % (paperAxisPeriodCellWord g hg a).length) :
    paperQuadrilateralSideNeighbor ((paperAxisPeriodCellWord g hg a)[i.val]'i.isLt) *
      paperQuadrilateralSideNeighbor ((paperAxisPeriodCellWord g hg a)[j.val]'j.isLt) ≠ 1 := by
  by_cases hi : i.val+1 < (paperAxisPeriodCellWord g hg a).length
  · rw [Nat.mod_eq_of_lt hi] at hnext
    have hh := paperAxisPeriodCellWord_no_immediate_inverse g hg a i.val hi
    simpa only [hnext] using hh
  · have hN := paperAxisPeriodCutPoints_three_le_of_off_sides g hg a ha
    have hilen : i.val+1 = (paperAxisPeriodCellWord g hg a).length := by have := i.isLt; omega
    have hj0 : j.val = 0 := by simpa only [hilen,Nat.mod_self] using hnext
    have hinext : i.val+1 = (paperAxisPeriodCutPoints g hg a).card-2 :=
      hilen.trans (paperAxisPeriodCellWord_length g hg a)
    have hilast : i.val = (paperAxisPeriodCutPoints g hg a).card-3 := by
      omega
    have hwrap : paperAxisPeriodCellLabelNat g hg a ((paperAxisPeriodCutPoints g hg a).card-2) =
        g * paperAxisPeriodCellLabelNat g hg a 0 := by
      have hh := paperAxisPeriodGapCellLabel_last_eq_period_mul_first g hg a ha
      simpa only [paperAxisPeriodCellLabelNat,min_self,Nat.zero_min,paperAxisFirstGapIndex,
        paperAxisLastGapIndex] using hh
    intro hback
    rw [paperAxisPeriodCellWord_getElem_ratio,paperAxisPeriodCellWord_getElem_ratio,
      hinext,hj0,hwrap] at hback
    have he : paperAxisPeriodCellLabelNat g hg a i.val =
        g * paperAxisPeriodCellLabelNat g hg a 1 := by
      apply inv_mul_eq_one.mp
      simpa only [Nat.zero_add,mul_assoc,mul_inv_cancel_left] using hback
    rw [hilast] at he
    exact paperAxisPeriodCellLabelNat_wrap_no_backtrack g hg a ha he

end Markov
