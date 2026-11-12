import Markov.PaperAxisWrapSubarc
import Markov.PaperAxisOrderedCellWord

/-! Actual non-backtracking of consecutive original-cell visits. Literal
neighbor intersections lie on the supporting side, so a hyperbolic axis cannot
return immediately across that same side. No simple-curve premise is used. -/
noncomputable section
open Set Topology
namespace Markov

/-- The two literal adjacent closed cells intersect exactly in the original
supporting geodesic side, from their proved opposite actual half-plane signs. -/
theorem paperQuadrilateral_neighbor_intersection_eq_side (k : Fin 4) :
    paperIdealQuadrilateral ∩
      (fun z : UpperHalfPlane => paperQuadrilateralSideNeighbor k • z) ''
        paperIdealQuadrilateral = paperQuadrilateralGeodesicSide k := by
  ext z
  constructor
  · rintro ⟨hz,hN⟩
    apply (paperQuadrilateralSideFunction_eq_zero_iff k z).mp
    exact le_antisymm (paperQuadrilateralSideFunction_nonpos_neighbor k z hN)
      (paperQuadrilateralSideFunction_nonneg k z hz)
  · intro hz
    exact ⟨paperQuadrilateralGeodesicSide_subset k hz,
      (paperQuadrilateral_side_point_cell_iff k z hz (paperQuadrilateralSideNeighbor k)).mpr (Or.inr rfl)⟩

private theorem noBacktrack_mem_side
    (δ : modularTraceSubgroup) (k : Fin 4) (x : UpperHalfPlane)
    (hδ : x ∈ (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral)
    (hN : x ∈ (fun z : UpperHalfPlane => (δ * paperQuadrilateralSideNeighbor k) • z) ''
      paperIdealQuadrilateral) :
    x ∈ (fun z : UpperHalfPlane => δ • z) '' paperQuadrilateralGeodesicSide k := by
  obtain ⟨z,hz,hzx⟩ := hδ
  obtain ⟨w,hw,hwx⟩ := hN
  change δ • z = x at hzx
  change (δ * paperQuadrilateralSideNeighbor k) • w = x at hwx
  have he : paperQuadrilateralSideNeighbor k • w = z := by
    apply (modularTraceSubgroup_isometry δ).injective
    simpa only [mul_smul] using hwx.trans hzx.symm
  have hs : z ∈ paperQuadrilateralGeodesicSide k :=
    paperQuadrilateral_neighbor_intersection_eq_side k ▸ ⟨hz, w, hw, he⟩
  exact ⟨z,hs,hzx⟩

/-- A fixed actual neighboring pair of full closed cells can meet an actual
hyperbolic axis at only one parameter, via the checked supporting-side theorem. -/
theorem modularHyperbolicAxis_neighbor_cell_intersection_subsingleton
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (δ : modularTraceSubgroup) (k : Fin 4) :
    {t : ℝ | modularHyperbolicAxis g hg t ∈
        (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral ∧
      modularHyperbolicAxis g hg t ∈
        (fun z : UpperHalfPlane => (δ * paperQuadrilateralSideNeighbor k) • z) ''
          paperIdealQuadrilateral}.Subsingleton := by
  intro s hs t ht
  exact modularHyperbolicAxis_paper_side_cut_subsingleton g hg δ k
    (noBacktrack_mem_side δ k _ hs.1 hs.2) (noBacktrack_mem_side δ k _ ht.1 ht.2)

/-- The actual shared table endpoint belongs to the closed cells of both
actual consecutive gap labels, including every actual boundary case. -/
theorem paperAxisPeriodGapCut_mem_both_label_cells
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i j : Fin ((paperAxisPeriodCutPoints g hg a).card-1)) (hij : j.val = i.val+1) :
    modularHyperbolicAxis g hg
        (paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i)) ∈
      (fun z : UpperHalfPlane => paperAxisPeriodGapCellLabel g hg a i • z) '' paperIdealQuadrilateral ∧
    modularHyperbolicAxis g hg
        (paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i)) ∈
      (fun z : UpperHalfPlane => paperAxisPeriodGapCellLabel g hg a j • z) '' paperIdealQuadrilateral := by
  have hmid : paperAxisGapRightIndex g hg a i = paperAxisGapLeftIndex g hg a j := by
    apply Fin.ext
    exact hij.symm
  have hi := (nonempty_Ioo.mp (paperAxisPeriodCutTable_gap_nonempty g hg a
    (paperAxisGapLeftIndex g hg a i) (paperAxisGapRightIndex g hg a i) rfl)).le
  have hj := (nonempty_Ioo.mp (paperAxisPeriodCutTable_gap_nonempty g hg a
    (paperAxisGapLeftIndex g hg a j) (paperAxisGapRightIndex g hg a j) rfl)).le
  constructor
  · exact (paperAxisPeriodGapCellLabel_spec g hg a i).2 _ ⟨hi,le_rfl⟩
  · apply (paperAxisPeriodGapCellLabel_spec g hg a j).2
    rw [hmid]
    exact ⟨le_rfl,hj⟩

/-- The actual geodesic cell itinerary cannot visit a cell, one other gap,
and immediately the same cell again. A pair of actual distinct cuts on one
supporting geodesic would contradict single intersection. -/
theorem paperAxisPeriodGapCellLabel_ne_two_steps
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i j k : Fin ((paperAxisPeriodCutPoints g hg a).card-1))
    (hij : j.val = i.val+1) (hjk : k.val = j.val+1) :
    paperAxisPeriodGapCellLabel g hg a i ≠ paperAxisPeriodGapCellLabel g hg a k := by
  intro he
  have hc := paperAxisPeriodGapCut_mem_both_label_cells g hg a i j hij
  have hd := paperAxisPeriodGapCut_mem_both_label_cells g hg a j k hjk
  rw [← he] at hd
  have hlt : paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i) <
      paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a j) := by
    apply paperAxisPeriodCutTable_strictMono
    change i.val+1 < j.val+1
    omega
  obtain ⟨l,hstep⟩ := paperAxisPeriodGapCellLabel_adjacent_step g hg a i j hij
  rcases hstep with hstep | hstep
  · have hp := modularHyperbolicAxis_neighbor_cell_intersection_subsingleton g hg
      (paperAxisPeriodGapCellLabel g hg a i) l
    have h1 := hc
    have h2 : modularHyperbolicAxis g hg
        (paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a j)) ∈
        (fun z : UpperHalfPlane => paperAxisPeriodGapCellLabel g hg a i • z) '' paperIdealQuadrilateral ∧
      modularHyperbolicAxis g hg
        (paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a j)) ∈
        (fun z : UpperHalfPlane => paperAxisPeriodGapCellLabel g hg a j • z) '' paperIdealQuadrilateral :=
      ⟨hd.2,hd.1⟩
    rw [hstep] at h1 h2
    exact hlt.ne (hp h1 h2)
  · have hback : paperAxisPeriodGapCellLabel g hg a i =
        paperAxisPeriodGapCellLabel g hg a j * paperQuadrilateralSideNeighbor l := by
      rw [hstep, mul_assoc, inv_mul_cancel, mul_one]
    have hp := modularHyperbolicAxis_neighbor_cell_intersection_subsingleton g hg
      (paperAxisPeriodGapCellLabel g hg a j) l
    have h1 : modularHyperbolicAxis g hg
        (paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i)) ∈
        (fun z : UpperHalfPlane => paperAxisPeriodGapCellLabel g hg a j • z) '' paperIdealQuadrilateral ∧
      modularHyperbolicAxis g hg
        (paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i)) ∈
        (fun z : UpperHalfPlane => paperAxisPeriodGapCellLabel g hg a i • z) '' paperIdealQuadrilateral :=
      ⟨hc.2,hc.1⟩
    have h2 := hd
    rw [hback] at h1 h2
    exact hlt.ne (hp h1 h2)

end Markov
