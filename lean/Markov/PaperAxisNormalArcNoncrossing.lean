import Markov.PaperAxisNormalArcEndpoints
import Markov.PaperQuadrilateralArcNoncrossing

/-! Actual internal finite-table Q-arcs have distinct endpoint values under
actual projected-period injectivity. The checked disk obstruction then derives
actual endpoint-chord noncrossing. No abstract endpoint ordering, matching,
normal diagram, empty-bigon operation, or classification field is assumed. -/

noncomputable section
open Set Topology
namespace Markov

/-- Each literal original side neighbor is an actual nonidentity deck matrix. -/
theorem paperQuadrilateralSideNeighbor_ne_one (k : Fin 4) :
    paperQuadrilateralSideNeighbor k ≠ 1 := by
  intro heq
  have hentry := congrArg (fun x : modularTraceSubgroup => ((x.val : IntMatrixTwo) 0 1)) heq
  fin_cases k
  · change ((paperGeneratorASL⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : IntMatrixTwo) 0 1 = 0 at hentry
    norm_num [Matrix.SpecialLinearGroup.coe_inv, paperGeneratorASL, paperGeneratorA,
      Matrix.adjugate_fin_two] at hentry
  · change ((paperGeneratorBSL⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : IntMatrixTwo) 0 1 = 0 at hentry
    norm_num [Matrix.SpecialLinearGroup.coe_inv, paperGeneratorBSL, paperGeneratorB,
      Matrix.adjugate_fin_two] at hentry
  · change paperGeneratorA 0 1 = 0 at hentry
    norm_num [paperGeneratorA] at hentry
  · change paperGeneratorB 0 1 = 0 at hentry
    norm_num [paperGeneratorB] at hentry

/-- The actual labels of adjacent constructed gaps are different. -/
theorem paperAxisPeriodGapCellLabel_adjacent_ne (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i j : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (hij : j.val = i.val+1) :
    paperAxisPeriodGapCellLabel g hg a i ≠ paperAxisPeriodGapCellLabel g hg a j := by
  intro heq
  obtain ⟨k, hstep | hstep⟩ := paperAxisPeriodGapCellLabel_adjacent_step g hg a i j hij
  · have hone : 1 = paperQuadrilateralSideNeighbor k :=
      mul_left_cancel (by simpa only [mul_one] using heq.trans hstep)
    exact paperQuadrilateralSideNeighbor_ne_one k hone.symm
  · have hone : 1 = (paperQuadrilateralSideNeighbor k)⁻¹ :=
      mul_left_cancel (by simpa only [mul_one] using heq.trans hstep)
    exact paperQuadrilateralSideNeighbor_ne_one k (inv_eq_one.mp hone.symm)

/-- All actual unit parameters stay in the actual CLOSED ordered gap. -/
theorem paperAxisPeriodGapParameter_mem_closed_gap (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (s : unitInterval) :
    paperAxisPeriodGapParameter g hg a i s ∈
      Icc (paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a i))
        (paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i)) := by
  have hlt := nonempty_Ioo.mp (paperAxisPeriodCutTable_gap_nonempty g hg a
    (paperAxisGapLeftIndex g hg a i) (paperAxisGapRightIndex g hg a i) rfl)
  have hs0 := s.property.1
  have hs1 := s.property.2
  dsimp only [paperAxisPeriodGapParameter]
  constructor <;> nlinarith

/-- An internal gap's entire closed real parameter segment is inside the open
metric period. The actual endpoints are not the period-base fragments. -/
theorem paperAxisPeriodGapParameter_internal_mem_period (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1))
    (hfirst : 0 < i.val) (hlast : i.val+2 < (paperAxisPeriodCutPoints g hg a).card)
    (s : unitInterval) :
    paperAxisPeriodGapParameter g hg a i s ∈ Ioo a (a+modularClosedGeodesicPeriod g) := by
  let p : Fin (paperAxisPeriodCutPoints g hg a).card := ⟨i.val-1, by have := i.isLt; omega⟩
  let n : Fin (paperAxisPeriodCutPoints g hg a).card := ⟨i.val+2, hlast⟩
  have hp : p < paperAxisGapLeftIndex g hg a i := by change i.val-1 < i.val; omega
  have hn : paperAxisGapRightIndex g hg a i < n := by change i.val+1 < i.val+2; omega
  have hleft := lt_of_le_of_lt (paperAxisPeriodCutTable_bounds g hg a p).1
    (paperAxisPeriodCutTable_strictMono g hg a hp)
  have hright := lt_of_lt_of_le (paperAxisPeriodCutTable_strictMono g hg a hn)
    (paperAxisPeriodCutTable_bounds g hg a n).2
  have hs := paperAxisPeriodGapParameter_mem_closed_gap g hg a i s
  exact ⟨hleft.trans_le hs.1, hs.2.trans_lt hright⟩

/-- Under actual projected-period injectivity, different internal Q-subarcs
have distinct points even at their CLOSED endpoints. If real parameters agree,
ordered gaps must be adjacent and equality of Q-points would force their actual
deck labels equal, contrary to the actual nonidentity side transition. -/
theorem paperAxisPeriodGapSubarc_internal_points_ne
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (hproject : Set.InjOn (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo a (a+modularClosedGeodesicPeriod g)))
    (i j : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (hij : i ≠ j)
    (hi0 : 0 < i.val) (hi1 : i.val+2 < (paperAxisPeriodCutPoints g hg a).card)
    (hj0 : 0 < j.val) (hj1 : j.val+2 < (paperAxisPeriodCutPoints g hg a).card)
    (s t : unitInterval) : paperAxisPeriodGapSubarc g hg a i s ≠ paperAxisPeriodGapSubarc g hg a j t := by
  intro heq
  have hproj := congrArg (fun z : paperIdealQuadrilateral => modularTraceQuotientMk z) heq
  simp only [paperAxisPeriodGapSubarc_project] at hproj
  have hparameter := hproject (paperAxisPeriodGapParameter_internal_mem_period g hg a i hi0 hi1 s)
    (paperAxisPeriodGapParameter_internal_mem_period g hg a j hj0 hj1 t) hproj
  have hlabels : paperAxisPeriodGapCellLabel g hg a i = paperAxisPeriodGapCellLabel g hg a j := by
    apply IsCancelSMul.right_cancel _ _ (paperAxisPeriodGapSubarc g hg a i s : UpperHalfPlane)
    calc
      _ = modularHyperbolicAxis g hg (paperAxisPeriodGapParameter g hg a i s) :=
        paperAxisPeriodGapSubarc_smul g hg a i s
      _ = modularHyperbolicAxis g hg (paperAxisPeriodGapParameter g hg a j t) := congrArg _ hparameter
      _ = paperAxisPeriodGapCellLabel g hg a j •
          (paperAxisPeriodGapSubarc g hg a j t : UpperHalfPlane) :=
        (paperAxisPeriodGapSubarc_smul g hg a j t).symm
      _ = _ := congrArg (fun z : paperIdealQuadrilateral =>
        paperAxisPeriodGapCellLabel g hg a j • (z:UpperHalfPlane)) heq.symm
  have hi := paperAxisPeriodGapParameter_mem_closed_gap g hg a i s
  have hj := paperAxisPeriodGapParameter_mem_closed_gap g hg a j t
  have hordered (u v : Fin ((paperAxisPeriodCutPoints g hg a).card - 1))
      (huv : u < v) :
      paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a u) ≤
        paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a v) := by
    apply (paperAxisPeriodCutTable g hg a).monotone
    change u.val+1 ≤ v.val
    change u.val < v.val at huv
    omega
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hends : paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i) =
        paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a j) := by
      apply le_antisymm (hordered i j hlt)
      exact hj.1.trans (hparameter ▸ hi.2)
    have hidx := congrArg Fin.val ((paperAxisPeriodCutTable g hg a).injective hends)
    have hadj : j.val=i.val+1 := hidx.symm
    exact paperAxisPeriodGapCellLabel_adjacent_ne g hg a i j hadj hlabels
  · have hends : paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a j) =
        paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a i) := by
      apply le_antisymm (hordered j i hgt)
      exact hi.1.trans (hparameter.symm ▸ hj.2)
    have hidx := congrArg Fin.val ((paperAxisPeriodCutTable g hg a).injective hends)
    have hadj : i.val=j.val+1 := hidx.symm
    exact paperAxisPeriodGapCellLabel_adjacent_ne g hg a j i hadj hlabels.symm

/-- The actual complex disk arc for each constructed actual Q-subarc. -/
def paperAxisPeriodGapDiskArc (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) : unitInterval → ℂ :=
  paperQuadrilateralDiskCoordinate ∘ paperAxisPeriodGapSubarc g hg a i

/-- Actual disjoint internal Q-subarcs of an actually period-injective projected
curve have noncrossing endpoint chords in their constructed disk coordinates.
The actual frontier, distinct-endpoint, strict-interior and disjointness inputs
are all discharged from the actual finite table and actual axis geometry. -/
theorem paperAxisPeriodGapDiskArc_no_transverse_chord_crossing
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (hproject : Set.InjOn (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo a (a+modularClosedGeodesicPeriod g)))
    (i j : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (hij : i ≠ j)
    (hi0 : 0 < i.val) (hi1 : i.val+2 < (paperAxisPeriodCutPoints g hg a).card)
    (hj0 : 0 < j.val) (hj1 : j.val+2 < (paperAxisPeriodCutPoints g hg a).card)
    (hd : (paperAxisPeriodGapDiskArc g hg a i 1-paperAxisPeriodGapDiskArc g hg a i 0).re *
        (paperAxisPeriodGapDiskArc g hg a j 1-paperAxisPeriodGapDiskArc g hg a j 0).im -
      (paperAxisPeriodGapDiskArc g hg a i 1-paperAxisPeriodGapDiskArc g hg a i 0).im *
        (paperAxisPeriodGapDiskArc g hg a j 1-paperAxisPeriodGapDiskArc g hg a j 0).re ≠ 0)
    (u v : unitInterval) (hu0 : 0 < (u:ℝ)) (hu1 : (u:ℝ) < 1)
    (hv0 : 0 < (v:ℝ)) (hv1 : (v:ℝ) < 1)
    (hchord : diskArcChord (paperAxisPeriodGapDiskArc g hg a i) u =
      diskArcChord (paperAxisPeriodGapDiskArc g hg a j) v) : False := by
  obtain ⟨ki, li, _, hiL, hiR, _, _⟩ := paperAxisPeriodGapSubarc_internal_endpoint_sides g hg a i hi0 hi1
  obtain ⟨kj, lj, _, hjL, hjR, _, _⟩ := paperAxisPeriodGapSubarc_internal_endpoint_sides g hg a j hj0 hj1
  exact paperQuadrilateral_disjoint_proper_arcs_no_transverse_chord_crossing
    (paperAxisPeriodGapSubarc g hg a i) (paperAxisPeriodGapSubarc g hg a j)
    (paperAxisPeriodGapSubarc g hg a i).continuous (paperAxisPeriodGapSubarc g hg a j).continuous
    (paperQuadrilateralGeodesicSide_subset_frontier ki hiL)
    (paperQuadrilateralGeodesicSide_subset_frontier li hiR)
    (paperQuadrilateralGeodesicSide_subset_frontier kj hjL)
    (paperQuadrilateralGeodesicSide_subset_frontier lj hjR)
    (fun h => (zero_ne_one : (0:unitInterval) ≠ 1) (paperAxisPeriodGapSubarc_injective g hg a i h))
    (fun h => (zero_ne_one : (0:unitInterval) ≠ 1) (paperAxisPeriodGapSubarc_injective g hg a j h))
    (paperAxisPeriodGapSubarc_strict g hg a i) (paperAxisPeriodGapSubarc_strict g hg a j)
    (fun s t _ _ => paperAxisPeriodGapSubarc_internal_points_ne g hg a hproject i j hij hi0 hi1 hj0 hj1 s t)
    (paperAxisPeriodGapSubarc_interiors_disjoint_of_projected_period_injective g hg a hproject i j hij)
    hd u v hu0 hu1 hv0 hv1 hchord

end Markov
