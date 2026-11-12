import Markov.PaperAxisNormalSubarcs
import Markov.PaperAxisAdjacentCellLabels

/-! Genuine boundary endpoints for the actual internal Q-subarcs. A returning
subarc with both endpoints on the same original side is ruled out by actual
single intersection of the periodic hyperbolic axis with that translated side.
The first and last gaps at the arbitrary period base are not asserted to have
boundary endpoints, and no matching or normal-form classification is assumed. -/

noncomputable section
open Set Topology
namespace Markov

/-- Actual frontier points have exactly one of the four literal side labels;
the ideal vertices are absent from UpperHalfPlane. -/
theorem paperQuadrilateral_frontier_existsUnique_side (z : UpperHalfPlane)
    (hz : z ∈ frontier paperIdealQuadrilateral) :
    ∃! k : Fin 4, z ∈ paperQuadrilateralGeodesicSide k := by
  obtain ⟨k, hk⟩ := mem_iUnion.mp (paperIdealQuadrilateral_frontier_eq_sides ▸ hz)
  refine ⟨k, hk, ?_⟩
  intro l hl
  by_contra hne
  exact disjoint_left.mp (paperQuadrilateralGeodesicSides_disjoint l k hne) hl hk

/-- An actual Q-point whose translate is on any actual translated original
side is on the actual Q-frontier. This is derived from strict representative
uniqueness and the free action, not supplied as an endpoint field. -/
theorem paperQuadrilateral_point_frontier_of_translated_side
    (z : paperIdealQuadrilateral) (δ ε : modularTraceSubgroup) (k : Fin 4)
    (hcut : δ • (z:UpperHalfPlane) ∈
      (fun w : UpperHalfPlane => ε • w) '' paperQuadrilateralGeodesicSide k) :
    (z:UpperHalfPlane) ∈ frontier paperIdealQuadrilateral := by
  refine ⟨subset_closure z.property, ?_⟩
  intro hinterior
  have hstrict : (z:UpperHalfPlane) ∈ paperIdealQuadrilateralStrictRegion :=
    paperIdealQuadrilateral_interior_eq_strictRegion ▸ hinterior
  obtain ⟨w, hw, heq⟩ := hcut
  have hlabels : δ = ε := paperStrictCell_label_unique δ ε (δ • (z:UpperHalfPlane))
    ⟨z, hstrict, rfl⟩ ⟨w, paperQuadrilateralGeodesicSide_subset k hw, heq⟩
  subst ε
  have hwz : w = (z:UpperHalfPlane) := (modularTraceSubgroup_isometry δ).injective heq
  have hfront := paperQuadrilateralGeodesicSide_subset_frontier k (hwz ▸ hw)
  exact hfront.2 hinterior

/-- Whenever an actual gap parameter is an actual side cut, its Q-subarc
point is a genuine original-cell frontier point. -/
theorem paperAxisPeriodGapSubarc_frontier_of_cut
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (s : unitInterval)
    (hcut : paperAxisPeriodGapParameter g hg a i s ∈ paperAxisSideCuts g hg) :
    (paperAxisPeriodGapSubarc g hg a i s : UpperHalfPlane) ∈ frontier paperIdealQuadrilateral := by
  obtain ⟨ε, k, hk⟩ := hcut
  apply paperQuadrilateral_point_frontier_of_translated_side
    (paperAxisPeriodGapSubarc g hg a i s) (paperAxisPeriodGapCellLabel g hg a i) ε k
  rw [paperAxisPeriodGapSubarc_smul]
  exact hk

/-- A genuine actual Q-subarc cannot return to the same literal original side.
Two such endpoint cuts would contradict the proved at-most-one actual
intersection with that translated geodesic side. -/
theorem paperAxisPeriodGapSubarc_endpoints_not_same_side
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (k : Fin 4) :
    ¬ ((paperAxisPeriodGapSubarc g hg a i 0 : UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide k ∧
      (paperAxisPeriodGapSubarc g hg a i 1 : UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide k) := by
  rintro ⟨hleft, hright⟩
  have hl : modularHyperbolicAxis g hg (paperAxisPeriodGapParameter g hg a i 0) ∈
      (fun z : UpperHalfPlane => paperAxisPeriodGapCellLabel g hg a i • z) ''
        paperQuadrilateralGeodesicSide k :=
    ⟨paperAxisPeriodGapSubarc g hg a i 0, hleft, paperAxisPeriodGapSubarc_smul g hg a i 0⟩
  have hr : modularHyperbolicAxis g hg (paperAxisPeriodGapParameter g hg a i 1) ∈
      (fun z : UpperHalfPlane => paperAxisPeriodGapCellLabel g hg a i • z) ''
        paperQuadrilateralGeodesicSide k :=
    ⟨paperAxisPeriodGapSubarc g hg a i 1, hright, paperAxisPeriodGapSubarc_smul g hg a i 1⟩
  have heq := modularHyperbolicAxis_paper_side_cut_subsingleton g hg
    (paperAxisPeriodGapCellLabel g hg a i) k hl hr
  have hlt : paperAxisPeriodGapParameter g hg a i 0 < paperAxisPeriodGapParameter g hg a i 1 := by
    simp only [paperAxisPeriodGapParameter, show ((0:unitInterval):ℝ)=0 from rfl,
      show ((1:unitInterval):ℝ)=1 from rfl, mul_zero, add_zero, mul_one, add_sub_cancel]
    exact nonempty_Ioo.mp (paperAxisPeriodCutTable_gap_nonempty g hg a
      (paperAxisGapLeftIndex g hg a i) (paperAxisGapRightIndex g hg a i) rfl)
  exact hlt.ne heq

/-- Every gap whose two endpoints are internal table cuts has actual uniquely
labelled boundary endpoints on TWO DIFFERENT literal original sides. Together
with the already constructed closed-embedded path and strict interior, these
are genuine proper normal subarcs, without a supplied matching field. -/
theorem paperAxisPeriodGapSubarc_internal_endpoint_sides
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1))
    (hfirst : 0 < i.val) (hlast : i.val + 2 < (paperAxisPeriodCutPoints g hg a).card) :
    ∃ k l : Fin 4, k ≠ l ∧
      (paperAxisPeriodGapSubarc g hg a i 0 : UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide k ∧
      (paperAxisPeriodGapSubarc g hg a i 1 : UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide l ∧
      (∀ k', (paperAxisPeriodGapSubarc g hg a i 0 : UpperHalfPlane) ∈
        paperQuadrilateralGeodesicSide k' → k' = k) ∧
      (∀ l', (paperAxisPeriodGapSubarc g hg a i 1 : UpperHalfPlane) ∈
        paperQuadrilateralGeodesicSide l' → l' = l) := by
  have hleftcut : paperAxisPeriodGapParameter g hg a i 0 ∈ paperAxisSideCuts g hg := by
    simp only [paperAxisPeriodGapParameter, show ((0:unitInterval):ℝ)=0 from rfl, mul_zero, add_zero]
    apply paperAxisPeriodCutTable_internal_mem_sideCuts
    · exact hfirst
    · change i.val + 1 < (paperAxisPeriodCutPoints g hg a).card
      omega
  have hrightcut : paperAxisPeriodGapParameter g hg a i 1 ∈ paperAxisSideCuts g hg := by
    simp only [paperAxisPeriodGapParameter, show ((1:unitInterval):ℝ)=1 from rfl,
      mul_one, add_sub_cancel]
    apply paperAxisPeriodCutTable_internal_mem_sideCuts
    · change 0 < i.val + 1
      omega
    · exact hlast
  obtain ⟨k, hk, hkuniq⟩ := paperQuadrilateral_frontier_existsUnique_side _
    (paperAxisPeriodGapSubarc_frontier_of_cut g hg a i 0 hleftcut)
  obtain ⟨l, hl, hluniq⟩ := paperQuadrilateral_frontier_existsUnique_side _
    (paperAxisPeriodGapSubarc_frontier_of_cut g hg a i 1 hrightcut)
  refine ⟨k, l, ?_, hk, hl, hkuniq, hluniq⟩
  intro heq
  exact paperAxisPeriodGapSubarc_endpoints_not_same_side g hg a i k ⟨hk, heq ▸ hl⟩

end Markov
