import Markov.PaperQuadrilateralFiniteAxisCuts
import Mathlib.Order.Interval.Set.Infinite

/-! Actual positive-period phase choices off every translated original edge,
and a literal strictly interior quadrilateral representative of that phase.
No normal-diagram or free-class identification is assumed. -/

noncomputable section
open Set Topology
namespace Markov

/-- In any nonempty open parameter interval an actual hyperbolic deck axis
has a phase on none of the four sides of any closed deck cell. -/
theorem modularHyperbolicAxis_exists_phase_off_paper_sides
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a b : ℝ) (hab : a < b) :
    ∃ t ∈ Ioo a b, ∀ δ : modularTraceSubgroup, ∀ k : Fin 4,
      modularHyperbolicAxis g hg t ∉
        (fun z : UpperHalfPlane => δ • z) '' paperQuadrilateralGeodesicSide k := by
  let S : Set ℝ := {t | t ∈ Icc a b ∧ ∃ δ : modularTraceSubgroup, ∃ k : Fin 4,
    modularHyperbolicAxis g hg t ∈
      (fun z : UpperHalfPlane => δ • z) '' paperQuadrilateralGeodesicSide k}
  have hS : S.Finite := modularHyperbolicAxis_finite_paper_side_cuts g hg a b
  obtain ⟨t, ht, hnot⟩ := ((Set.Ioo_infinite hab).diff hS).nonempty
  refine ⟨t, ht, ?_⟩
  intro δ k hk
  exact hnot ⟨⟨ht.1.le, ht.2.le⟩, δ, k, hk⟩

/-- A genuine phase strictly inside one metric period has an actual original
quadrilateral representative satisfying all four STRICT inequalities. The deck
element and point are constructed by the checked actual quotient coverage. -/
theorem modularHyperbolicAxis_exists_strict_paper_representative
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    ∃ t ∈ Ioo 0 (modularClosedGeodesicPeriod g),
      ∃ δ : modularTraceSubgroup, ∃ z : UpperHalfPlane,
        δ • z = modularHyperbolicAxis g hg t ∧
        -1 < z.re ∧ z.re < 1 ∧
        0 < z.re ^ 2 + z.re + z.im ^ 2 ∧
        0 < z.re ^ 2 - z.re + z.im ^ 2 := by
  obtain ⟨t, ht, hoff⟩ := modularHyperbolicAxis_exists_phase_off_paper_sides
    g hg 0 (modularClosedGeodesicPeriod g) (modularClosedGeodesicPeriod_pos g hg)
  obtain ⟨z, hz, hproj⟩ := paperIdealQuadrilateral_quotient_coverage
    (modularTraceQuotientMk (modularHyperbolicAxis g hg t))
  obtain ⟨δ, hδ⟩ := (modularTraceQuotientMk_eq_iff (modularHyperbolicAxis g hg t) z).mp hproj.symm
  have hside (k : Fin 4) : z ∉ paperQuadrilateralGeodesicSide k := by
    intro hk
    exact hoff δ k ⟨z, hk, hδ⟩
  have h0 : z.re ≠ 1 := hside 0
  have h1 : z.re ≠ -1 := hside 1
  have h2 : z.re ^ 2 + z.re + z.im ^ 2 ≠ 0 := hside 2
  have h3 : z.re ^ 2 - z.re + z.im ^ 2 ≠ 0 := hside 3
  rcases hz with ⟨hl, hr, hleft, hright⟩
  exact ⟨t, ht, δ, z, hδ, lt_of_le_of_ne hl h1.symm,
    lt_of_le_of_ne hr h0, lt_of_le_of_ne hleft h2.symm,
    lt_of_le_of_ne hright h3.symm⟩

end Markov
