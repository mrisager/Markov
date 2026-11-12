import Markov.PaperAxisCutTable
import Markov.PaperCutFreeGapCell

/-! Actual finite cell itinerary of an actual hyperbolic axis over a metric
period. The gap labels are constructed from the proved cut-free intervals;
neither an itinerary nor any cyclic-word/classification property is assumed. -/

noncomputable section
open Set Topology
namespace Markov

theorem paperAxisPeriodCutPoints_two_le (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    2 ≤ (paperAxisPeriodCutPoints g hg a).card := by
  by_contra hn
  have hsmall : (paperAxisPeriodCutPoints g hg a).card ≤ 1 := by omega
  have ha : a ∈ paperAxisPeriodCutPoints g hg a :=
    (mem_finiteRealCutPoints _ _ _ _ a).mpr (Or.inl rfl)
  have hb : a + modularClosedGeodesicPeriod g ∈ paperAxisPeriodCutPoints g hg a :=
    (mem_finiteRealCutPoints _ _ _ _ _).mpr (Or.inr (Or.inl rfl))
  have heq := Finset.card_le_one.mp hsmall a ha (a + modularClosedGeodesicPeriod g) hb
  have hpos := modularClosedGeodesicPeriod_pos g hg
  linarith

/-- The constructed metric-period table has at least one actual gap. -/
theorem paperAxisPeriodGap_count_pos (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    0 < (paperAxisPeriodCutPoints g hg a).card - 1 := by
  have := paperAxisPeriodCutPoints_two_le g hg a
  omega

def paperAxisGapLeftIndex (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) :
    Fin (paperAxisPeriodCutPoints g hg a).card :=
  ⟨i.val, by have := i.isLt; omega⟩

def paperAxisGapRightIndex (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) :
    Fin (paperAxisPeriodCutPoints g hg a).card :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

/-- Each consecutive actual open gap lies in a single translated strict cell;
the entire actual closed segment lies in that same closed cell. -/
theorem paperAxisPeriodCutTable_consecutive_cell
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i j : Fin (paperAxisPeriodCutPoints g hg a).card) (hij : j.val = i.val + 1) :
    ∃ δ : modularTraceSubgroup,
      (∀ t ∈ Ioo (paperAxisPeriodCutTable g hg a i) (paperAxisPeriodCutTable g hg a j),
        modularHyperbolicAxis g hg t ∈
          (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateralStrictRegion) ∧
      ∀ t ∈ Icc (paperAxisPeriodCutTable g hg a i) (paperAxisPeriodCutTable g hg a j),
        modularHyperbolicAxis g hg t ∈
          (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral := by
  have hab := nonempty_Ioo.mp (paperAxisPeriodCutTable_gap_nonempty g hg a i j hij)
  apply continuous_paper_cutFree_gap_cell _ (modularHyperbolicAxis_isometry g hg).continuous _ _ hab
  intro t ht δ k hk
  exact paperAxisPeriodCutTable_gap_off_sides g hg a i j hij t ht ⟨δ, k, hk⟩

/-- Every finite gap receives an ACTUAL deck label chosen from proved geometry. -/
def paperAxisPeriodGapCellLabel (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) : modularTraceSubgroup :=
  (paperAxisPeriodCutTable_consecutive_cell g hg a
    (paperAxisGapLeftIndex g hg a i) (paperAxisGapRightIndex g hg a i) rfl).choose

theorem paperAxisPeriodGapCellLabel_spec (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) :
    (∀ t ∈ Ioo (paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a i))
        (paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i)),
      modularHyperbolicAxis g hg t ∈
        (fun z : UpperHalfPlane => paperAxisPeriodGapCellLabel g hg a i • z) ''
          paperIdealQuadrilateralStrictRegion) ∧
    ∀ t ∈ Icc (paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a i))
        (paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i)),
      modularHyperbolicAxis g hg t ∈
        (fun z : UpperHalfPlane => paperAxisPeriodGapCellLabel g hg a i • z) ''
          paperIdealQuadrilateral :=
  (paperAxisPeriodCutTable_consecutive_cell g hg a
    (paperAxisGapLeftIndex g hg a i) (paperAxisGapRightIndex g hg a i) rfl).choose_spec

/-- The actual itinerary label is unique even among labels whose CLOSED cell
contains the whole gap. No arbitrary label choice can change the itinerary. -/
theorem paperAxisPeriodGapCellLabel_unique (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (ε : modularTraceSubgroup)
    (hε : ∀ t ∈ Icc (paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a i))
        (paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i)),
      modularHyperbolicAxis g hg t ∈
        (fun z : UpperHalfPlane => ε • z) '' paperIdealQuadrilateral) :
    paperAxisPeriodGapCellLabel g hg a i = ε := by
  obtain ⟨t, ht⟩ := paperAxisPeriodCutTable_gap_nonempty g hg a
    (paperAxisGapLeftIndex g hg a i) (paperAxisGapRightIndex g hg a i) rfl
  exact paperStrictCell_label_unique _ ε _
    ((paperAxisPeriodGapCellLabel_spec g hg a i).1 t ht)
    (hε t ⟨ht.1.le, ht.2.le⟩)

end Markov
