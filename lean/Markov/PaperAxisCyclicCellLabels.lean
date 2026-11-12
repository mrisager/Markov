import Markov.PaperAxisAdjacentCellLabels

/-! Actual first/last cell labels close up by the actual deck period action.
Only genuine off-cut geometry, endpoint inclusions and strict-label uniqueness
are used; there is no matrix-word or homology premise. -/
noncomputable section
open Set Topology
namespace Markov

/-- The first actual gap index of the nonempty constructed period table. -/
def paperAxisFirstGapIndex (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    Fin ((paperAxisPeriodCutPoints g hg a).card - 1) :=
  ⟨0, paperAxisPeriodGap_count_pos g hg a⟩

/-- The last actual gap index, retaining the actual finite cardinality. -/
def paperAxisLastGapIndex (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    Fin ((paperAxisPeriodCutPoints g hg a).card - 1) :=
  ⟨(paperAxisPeriodCutPoints g hg a).card - 2, by
    have := paperAxisPeriodCutPoints_two_le g hg a
    omega⟩

private theorem cyclicCells_first_closed
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    modularHyperbolicAxis g hg a ∈
      (fun z : UpperHalfPlane =>
        paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a) • z) ''
          paperIdealQuadrilateral := by
  have he : paperAxisPeriodCutTable g hg a
      (paperAxisGapLeftIndex g hg a (paperAxisFirstGapIndex g hg a)) = a :=
    (paperAxisPeriodCutTable_endpoints g hg a).1
  apply (paperAxisPeriodGapCellLabel_spec g hg a (paperAxisFirstGapIndex g hg a)).2 a
  rw [he]
  exact ⟨le_rfl, (paperAxisPeriodCutTable_bounds g hg a _).1⟩

private theorem cyclicCells_last_closed
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    modularHyperbolicAxis g hg (a + modularClosedGeodesicPeriod g) ∈
      (fun z : UpperHalfPlane =>
        paperAxisPeriodGapCellLabel g hg a (paperAxisLastGapIndex g hg a) • z) ''
          paperIdealQuadrilateral := by
  have hidx : paperAxisGapRightIndex g hg a (paperAxisLastGapIndex g hg a) =
      ⟨(paperAxisPeriodCutPoints g hg a).card-1,
        Nat.sub_lt (paperAxisPeriodCutPoints_card_pos g hg a) (by decide)⟩ := by
    apply Fin.ext
    have := paperAxisPeriodCutPoints_two_le g hg a
    change (paperAxisPeriodCutPoints g hg a).card-2+1 =
      (paperAxisPeriodCutPoints g hg a).card-1
    omega
  have he : paperAxisPeriodCutTable g hg a
      (paperAxisGapRightIndex g hg a (paperAxisLastGapIndex g hg a)) =
        a + modularClosedGeodesicPeriod g := by
    rw [hidx]
    exact (paperAxisPeriodCutTable_endpoints g hg a).2
  apply (paperAxisPeriodGapCellLabel_spec g hg a (paperAxisLastGapIndex g hg a)).2
    (a + modularClosedGeodesicPeriod g)
  rw [he]
  exact ⟨(paperAxisPeriodCutTable_bounds g hg a _).2, le_rfl⟩

/-- An actual off-cut base makes the LAST chosen gap label equal to the actual
period deck element times the FIRST label, with the literal multiplication order. -/
theorem paperAxisPeriodGapCellLabel_last_eq_period_mul_first
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) :
    paperAxisPeriodGapCellLabel g hg a (paperAxisLastGapIndex g hg a) =
      g * paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a) := by
  have hoff : ∀ δ : modularTraceSubgroup, ∀ k : Fin 4,
      modularHyperbolicAxis g hg a ∉
        (fun z : UpperHalfPlane => δ • z) '' paperQuadrilateralGeodesicSide k :=
    fun δ k h => ha ⟨δ, k, h⟩
  obtain ⟨δ, hδ, _⟩ := paperStrictCell_existsUnique_of_off_sides
    (modularHyperbolicAxis g hg a) hoff
  have hfirst : δ = paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a) :=
    paperStrictCell_label_unique δ _ _ hδ (cyclicCells_first_closed g hg a)
  have hend : modularHyperbolicAxis g hg (a + modularClosedGeodesicPeriod g) ∈
      (fun z : UpperHalfPlane => (g * δ) • z) '' paperIdealQuadrilateralStrictRegion := by
    obtain ⟨z, hz, heq⟩ := hδ
    change δ • z = modularHyperbolicAxis g hg a at heq
    refine ⟨z, hz, ?_⟩
    change (g * δ) • z = modularHyperbolicAxis g hg (a + modularClosedGeodesicPeriod g)
    rw [mul_smul, heq, modularHyperbolicAxis_action]
  have hlast := paperStrictCell_label_unique (g * δ) _ _ hend (cyclicCells_last_closed g hg a)
  rw [hfirst] at hlast
  exact hlast.symm

end Markov
