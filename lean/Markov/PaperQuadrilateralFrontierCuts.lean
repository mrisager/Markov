import Markov.PaperAxisGenericPhase

/-! Actual strict original-cell interior and finite true frontier cut times.
Only the proved frontier inclusion needed here is asserted; no converse side
frontier characterization or normal-diagram classification is assumed. -/

noncomputable section
open Set Topology
namespace Markov

/-- The literal four strict inequalities in the original upper-half-plane chart. -/
def paperIdealQuadrilateralStrictRegion : Set UpperHalfPlane :=
  {z | -1 < z.re ∧ z.re < 1 ∧ 0 < z.re ^ 2 + z.re + z.im ^ 2 ∧
    0 < z.re ^ 2 - z.re + z.im ^ 2}

theorem paperIdealQuadrilateralStrictRegion_isOpen :
    IsOpen paperIdealQuadrilateralStrictRegion := by
  have hr : Continuous (fun z : UpperHalfPlane => z.re) := by fun_prop
  have hl : Continuous (fun z : UpperHalfPlane => z.re ^ 2 + z.re + z.im ^ 2) := by fun_prop
  have hright : Continuous (fun z : UpperHalfPlane => z.re ^ 2 - z.re + z.im ^ 2) := by fun_prop
  exact (isOpen_lt continuous_const hr).inter ((isOpen_lt hr continuous_const).inter
    ((isOpen_lt continuous_const hl).inter (isOpen_lt continuous_const hright)))

theorem paperIdealQuadrilateralStrictRegion_subset :
    paperIdealQuadrilateralStrictRegion ⊆ paperIdealQuadrilateral := by
  rintro z ⟨hl, hr, hleft, hright⟩
  exact ⟨hl.le, hr.le, hleft.le, hright.le⟩

theorem paperIdealQuadrilateralStrictRegion_subset_interior :
    paperIdealQuadrilateralStrictRegion ⊆ interior paperIdealQuadrilateral :=
  interior_maximal paperIdealQuadrilateralStrictRegion_subset
    paperIdealQuadrilateralStrictRegion_isOpen

/-- Every actual topological frontier point lies on one of the four literal
original sides. Closedness and the proved strict open region discharge this. -/
theorem paperIdealQuadrilateral_frontier_subset_sides :
    frontier paperIdealQuadrilateral ⊆ ⋃ k : Fin 4, paperQuadrilateralGeodesicSide k := by
  intro z hz
  change z ∈ closure paperIdealQuadrilateral ∧ z ∉ interior paperIdealQuadrilateral at hz
  rw [paperIdealQuadrilateral_isClosed.closure_eq] at hz
  by_contra hnot
  have hside (k : Fin 4) : z ∉ paperQuadrilateralGeodesicSide k :=
    fun hk => hnot (mem_iUnion.mpr ⟨k, hk⟩)
  have h0 : z.re ≠ 1 := hside 0
  have h1 : z.re ≠ -1 := hside 1
  have h2 : z.re ^ 2 + z.re + z.im ^ 2 ≠ 0 := hside 2
  have h3 : z.re ^ 2 - z.re + z.im ^ 2 ≠ 0 := hside 3
  obtain ⟨hl, hr, hleft, hright⟩ := hz.1
  apply hz.2
  apply paperIdealQuadrilateralStrictRegion_subset_interior
  exact ⟨lt_of_le_of_ne hl h1.symm, lt_of_le_of_ne hr h0,
    lt_of_le_of_ne hleft h2.symm, lt_of_le_of_ne hright h3.symm⟩

/-- Actual translated-frontier cut times, not only edge candidates, are
finite for every compact interval on every actual hyperbolic deck axis. -/
theorem modularHyperbolicAxis_finite_paper_frontier_cuts
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a b : ℝ) :
    {t : ℝ | t ∈ Icc a b ∧ ∃ δ : modularTraceSubgroup,
      modularHyperbolicAxis g hg t ∈
        (fun z : UpperHalfPlane => δ • z) '' frontier paperIdealQuadrilateral}.Finite := by
  apply (modularHyperbolicAxis_finite_paper_side_cuts g hg a b).subset
  rintro t ⟨ht, δ, z, hz, heq⟩
  obtain ⟨k, hk⟩ := mem_iUnion.mp (paperIdealQuadrilateral_frontier_subset_sides hz)
  exact ⟨ht, δ, k, z, hk, heq⟩

/-- An actual phase strictly inside the actual positive metric period has a
representative in the genuine topological INTERIOR of the original cell. -/
theorem modularHyperbolicAxis_exists_interior_paper_representative
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    ∃ t ∈ Ioo 0 (modularClosedGeodesicPeriod g),
      ∃ δ : modularTraceSubgroup, ∃ z ∈ interior paperIdealQuadrilateral,
        δ • z = modularHyperbolicAxis g hg t := by
  obtain ⟨t, ht, δ, z, heq, hstrict⟩ :=
    modularHyperbolicAxis_exists_strict_paper_representative g hg
  exact ⟨t, ht, δ, z, paperIdealQuadrilateralStrictRegion_subset_interior hstrict, heq⟩

end Markov
