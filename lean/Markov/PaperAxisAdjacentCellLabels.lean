import Markov.PaperAxisCellItinerary
import Markov.PaperGeodesicCellTransition

/-! Actual consecutive finite-itinerary labels differ by an original side
neighbor or its inverse. The internal cut, actual side witness and local
transition are all derived from the constructed table and actual axis. -/
noncomputable section
open Set Topology
namespace Markov

/-- Every nonendpoint internal index of the constructed metric-period table
is an actual original-side cut, rather than a table endpoint adjoined by sorting. -/
theorem paperAxisPeriodCutTable_internal_mem_sideCuts
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (m : Fin (paperAxisPeriodCutPoints g hg a).card)
    (hfirst : 0 < m.val) (hlast : m.val + 1 < (paperAxisPeriodCutPoints g hg a).card) :
    paperAxisPeriodCutTable g hg a m ∈ paperAxisSideCuts g hg := by
  let p : Fin (paperAxisPeriodCutPoints g hg a).card := ⟨m.val-1, by have := m.isLt; omega⟩
  let n : Fin (paperAxisPeriodCutPoints g hg a).card := ⟨m.val+1, hlast⟩
  have hpm : p < m := by change m.val-1 < m.val; omega
  have hmn : m < n := by change m.val < m.val+1; omega
  have ha : a < paperAxisPeriodCutTable g hg a m :=
    lt_of_le_of_lt (paperAxisPeriodCutTable_bounds g hg a p).1
      (paperAxisPeriodCutTable_strictMono g hg a hpm)
  have hb : paperAxisPeriodCutTable g hg a m < a + modularClosedGeodesicPeriod g :=
    lt_of_lt_of_le (paperAxisPeriodCutTable_strictMono g hg a hmn)
      (paperAxisPeriodCutTable_bounds g hg a n).2
  have hmem : paperAxisPeriodCutTable g hg a m ∈ paperAxisPeriodCutPoints g hg a := by
    change paperAxisPeriodCutTable g hg a m ∈ (paperAxisPeriodCutPoints g hg a : Set ℝ)
    rw [← paperAxisPeriodCutTable_range]
    exact ⟨m, rfl⟩
  rcases (mem_finiteRealCutPoints _ _ _ _ _).mp hmem with he | he | hcut
  · exact (ha.ne' he).elim
  · exact (hb.ne he).elim
  · exact hcut.2

/-- The internal cut between two actual adjacent gaps supplies an actual
side-line intersection. Its genuine local cell transition identifies the two
ACTUAL chosen gap labels, in one of the two geometric orientations. -/
theorem paperAxisPeriodGapCellLabel_adjacent_side_witness
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i j : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (hij : j.val = i.val+1) :
    ∃ δ : modularTraceSubgroup, ∃ k : Fin 4, ∃ v : ℝ,
      modularHyperbolicAxis g hg
          (paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i)) =
        δ • paperQuadrilateralGeodesicSideLine k v ∧
      ((paperAxisPeriodGapCellLabel g hg a i = δ ∧
          paperAxisPeriodGapCellLabel g hg a j = δ * paperQuadrilateralSideNeighbor k) ∨
        (paperAxisPeriodGapCellLabel g hg a j = δ ∧
          paperAxisPeriodGapCellLabel g hg a i = δ * paperQuadrilateralSideNeighbor k)) := by
  have hmid : paperAxisGapRightIndex g hg a i = paperAxisGapLeftIndex g hg a j := by
    apply Fin.ext
    change i.val+1 = j.val
    omega
  let l := paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a i)
  let c := paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i)
  let r := paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a j)
  have hlc : l < c := nonempty_Ioo.mp (paperAxisPeriodCutTable_gap_nonempty g hg a
    (paperAxisGapLeftIndex g hg a i) (paperAxisGapRightIndex g hg a i) rfl)
  have hcr : c < r := by
    have hh := nonempty_Ioo.mp (paperAxisPeriodCutTable_gap_nonempty g hg a
      (paperAxisGapLeftIndex g hg a j) (paperAxisGapRightIndex g hg a j) rfl)
    rw [← hmid] at hh
    exact hh
  have hcut : c ∈ paperAxisSideCuts g hg := by
    apply paperAxisPeriodCutTable_internal_mem_sideCuts g hg a (paperAxisGapRightIndex g hg a i)
    · change 0 < i.val+1
      omega
    · change i.val+1+1 < (paperAxisPeriodCutPoints g hg a).card
      have hj := j.isLt
      omega
  obtain ⟨δ, k, z, hz, heq⟩ := hcut
  obtain ⟨v, hv⟩ := (paperQuadrilateralGeodesicSideLine_range k).symm ▸ hz
  have hpoint : modularHyperbolicAxis g hg c = δ • paperQuadrilateralGeodesicSideLine k v :=
    heq.symm.trans (congrArg (fun z : UpperHalfPlane => δ • z) hv.symm)
  obtain ⟨ε, hε, hcases⟩ := modularHyperbolicAxis_paper_side_cell_transition g hg δ k c v hpoint
  obtain ⟨x, hxlo, hxc⟩ := exists_between (max_lt hlc (by linarith : c-ε < c))
  obtain ⟨y, hcy, hyhi⟩ := exists_between (lt_min hcr (by linarith : c < c+ε))
  have hlx : l < x := lt_of_le_of_lt (le_max_left l (c-ε)) hxlo
  have hεx : c-ε < x := lt_of_le_of_lt (le_max_right l (c-ε)) hxlo
  have hyr : y < r := lt_of_lt_of_le hyhi (min_le_left r (c+ε))
  have hyε : y < c+ε := lt_of_lt_of_le hyhi (min_le_right r (c+ε))
  have hxstrict := (paperAxisPeriodGapCellLabel_spec g hg a i).1 x ⟨hlx, hxc⟩
  have hystrict : modularHyperbolicAxis g hg y ∈
      (fun z : UpperHalfPlane => paperAxisPeriodGapCellLabel g hg a j • z) ''
        paperIdealQuadrilateralStrictRegion := by
    apply (paperAxisPeriodGapCellLabel_spec g hg a j).1
    rw [← hmid]
    exact ⟨hcy, hyr⟩
  refine ⟨δ, k, v, hpoint, ?_⟩
  rcases hcases with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · left
    exact ⟨paperStrictCell_label_unique _ δ _ hxstrict
        (Set.image_mono interior_subset (hleft x ⟨hεx, hxc⟩)),
      paperStrictCell_label_unique _ (δ * paperQuadrilateralSideNeighbor k) _ hystrict
        (Set.image_mono interior_subset (hright y ⟨hcy, hyε⟩))⟩
  · right
    exact ⟨paperStrictCell_label_unique _ δ _ hystrict
        (Set.image_mono interior_subset (hright y ⟨hcy, hyε⟩)),
      paperStrictCell_label_unique _ (δ * paperQuadrilateralSideNeighbor k) _ hxstrict
        (Set.image_mono interior_subset (hleft x ⟨hεx, hxc⟩))⟩

/-- Every adjacent step of the actual finite deck-cell itinerary is literal
right multiplication by one actual original-side neighbor or its inverse. -/
theorem paperAxisPeriodGapCellLabel_adjacent_step
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i j : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (hij : j.val = i.val+1) :
    ∃ k : Fin 4,
      paperAxisPeriodGapCellLabel g hg a j =
          paperAxisPeriodGapCellLabel g hg a i * paperQuadrilateralSideNeighbor k ∨
        paperAxisPeriodGapCellLabel g hg a j =
          paperAxisPeriodGapCellLabel g hg a i * (paperQuadrilateralSideNeighbor k)⁻¹ := by
  obtain ⟨δ, k, v, _, hcases⟩ := paperAxisPeriodGapCellLabel_adjacent_side_witness g hg a i j hij
  refine ⟨k, ?_⟩
  rcases hcases with ⟨hi, hj⟩ | ⟨hj, hi⟩
  · exact Or.inl (by rw [hi, hj])
  · right
    rw [hi, hj, mul_assoc, mul_inv_cancel, mul_one]

end Markov
