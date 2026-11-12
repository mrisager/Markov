import Markov.PaperQuadrilateralFrontierCuts
import Markov.QuadrilateralBoundaryExact

/-! Exact strict-cell representative uniqueness and actual positive-period
exit from the initial closed cell. The completed closed return classifier is
reused; no new boundary-identification premise or cut-word claim is made. -/

noncomputable section
open Set Topology
namespace Markov

/-- A strictly interior-inequality representative has no nonidentity deck
return to the CLOSED original cell. All four original side conditions are kept. -/
theorem paperIdealQuadrilateralStrictRegion_return_eq_one
    (g : modularTraceSubgroup) (z : UpperHalfPlane)
    (hz : z ∈ paperIdealQuadrilateralStrictRegion)
    (hgz : g • z ∈ paperIdealQuadrilateral) : g = 1 := by
  have hzQ := paperIdealQuadrilateralStrictRegion_subset hz
  obtain ⟨i, hi⟩ := paperIdealQuadrilateral_return_word g.val g.property z hzQ hgz
  have hret : paperQuadrilateralSideReturnWordAt i • z ∈ paperIdealQuadrilateral := by
    rw [← hi]
    exact hgz
  rcases hz with ⟨hl, hr, hleft, hright⟩
  fin_cases i
  · exact Subtype.ext hi
  · have hs := (paperGeneratorA_quadrilateral_return_iff z hzQ).mp hret
    exact (hr.ne hs).elim
  · have hs := (paperGeneratorA_inv_quadrilateral_return_iff z hzQ).mp hret
    exact ((ne_of_gt hleft) hs).elim
  · have hs := (paperGeneratorB_quadrilateral_return_iff z hzQ).mp hret
    exact (hl.ne' hs).elim
  · have hs := (paperGeneratorB_inv_quadrilateral_return_iff z hzQ).mp hret
    exact ((ne_of_gt hright) hs).elim

/-- The actual orbit of a strict representative meets the closed original
cell in that one point, including possible boundary candidates. -/
theorem paperIdealQuadrilateralStrictRegion_quotient_unique
    (z w : UpperHalfPlane) (hz : z ∈ paperIdealQuadrilateralStrictRegion)
    (hw : w ∈ paperIdealQuadrilateral)
    (hproj : modularTraceQuotientMk z = modularTraceQuotientMk w) : z = w := by
  obtain ⟨g, hg⟩ := (modularTraceQuotientMk_eq_iff w z).mp hproj.symm
  have hret : g • z ∈ paperIdealQuadrilateral := hg.symm ▸ hw
  have hone := paperIdealQuadrilateralStrictRegion_return_eq_one g z hz hret
  simpa only [hone, one_smul] using hg

/-- A positive-period projected isometric line starting at an actual strict
cell representative ends that period OUTSIDE the same full closed deck cell. -/
theorem periodicIsometricLine_period_endpoint_outside_start_cell
    (F : ℝ → UpperHalfPlane) (hF : Isometry F) (L : ℝ) (hL : 0 < L)
    (hperiod : Function.Periodic (fun t => modularTraceQuotientMk (F t)) L)
    (t : ℝ) (δ : modularTraceSubgroup) (z : UpperHalfPlane)
    (hz : z ∈ paperIdealQuadrilateralStrictRegion) (hstart : δ • z = F t) :
    F (t+L) ∉ (fun w : UpperHalfPlane => δ • w) '' paperIdealQuadrilateral := by
  rintro ⟨w, hw, heq⟩
  have hproj : modularTraceQuotientMk z = modularTraceQuotientMk w := by
    calc
      _ = modularTraceQuotientMk (δ • z) := (modularTraceQuotientMk_smul δ z).symm
      _ = modularTraceQuotientMk (F t) := congrArg modularTraceQuotientMk hstart
      _ = modularTraceQuotientMk (F (t+L)) := (hperiod t).symm
      _ = modularTraceQuotientMk (δ • w) := congrArg modularTraceQuotientMk heq.symm
      _ = _ := modularTraceQuotientMk_smul δ w
  have hzw := paperIdealQuadrilateralStrictRegion_quotient_unique z w hz hw hproj
  rw [← hzw] at heq
  have htime : t+L = t := hF.injective (heq.symm.trans hstart)
  linarith

/-- The actual interior phase can be chosen with its complete-period endpoint
outside the initial cell. This prepares a genuine nonempty finite cut diagram,
but does not construct that diagram or identify a cyclic word. -/
theorem modularHyperbolicAxis_exists_strict_phase_with_period_exit
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    ∃ t ∈ Ioo 0 (modularClosedGeodesicPeriod g),
      ∃ δ : modularTraceSubgroup, ∃ z ∈ paperIdealQuadrilateralStrictRegion,
        δ • z = modularHyperbolicAxis g hg t ∧
        modularHyperbolicAxis g hg (t+modularClosedGeodesicPeriod g) ∉
          (fun w : UpperHalfPlane => δ • w) '' paperIdealQuadrilateral := by
  obtain ⟨t, ht, δ, z, heq, hstrict⟩ :=
    modularHyperbolicAxis_exists_strict_paper_representative g hg
  refine ⟨t, ht, δ, z, hstrict, heq, ?_⟩
  exact periodicIsometricLine_period_endpoint_outside_start_cell
    (modularHyperbolicAxis g hg) (modularHyperbolicAxis_isometry g hg)
    (modularClosedGeodesicPeriod g) (modularClosedGeodesicPeriod_pos g hg)
    (modularClosedGeodesic_periodic g hg) t δ z hstrict heq

end Markov
