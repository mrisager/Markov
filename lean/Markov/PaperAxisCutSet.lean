import Markov.PaperStrictCellReturns

/-! The literal periodic set of all actual original-side cuts of a hyperbolic
deck axis. Finiteness and cut-free period endpoints are proved, not fields. -/

noncomputable section
open Set Topology
namespace Markov

/-- Every deck and all four original side labels occur in this actual set. -/
def paperAxisSideCuts (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) : Set ℝ :=
  {t | ∃ δ : modularTraceSubgroup, ∃ k : Fin 4,
    modularHyperbolicAxis g hg t ∈
      (fun z : UpperHalfPlane => δ • z) '' paperQuadrilateralGeodesicSide k}

theorem paperAxisSideCuts_finite_Icc
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a b : ℝ) :
    (Icc a b ∩ paperAxisSideCuts g hg).Finite := by
  exact modularHyperbolicAxis_finite_paper_side_cuts g hg a b

theorem paperAxisSideCuts_finite_Ioo
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a b : ℝ) :
    (Ioo a b ∩ paperAxisSideCuts g hg).Finite := by
  apply (paperAxisSideCuts_finite_Icc g hg a b).subset
  rintro t ⟨ht, hc⟩
  exact ⟨⟨ht.1.le, ht.2.le⟩, hc⟩

/-- Literal multiplication of the deck labels proves exact period invariance
of the actual cut set. No canonical word or side-choice premise is used. -/
theorem paperAxisSideCuts_period_iff
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (t : ℝ) :
    t + modularClosedGeodesicPeriod g ∈ paperAxisSideCuts g hg ↔
      t ∈ paperAxisSideCuts g hg := by
  constructor
  · rintro ⟨δ, k, z, hz, heq⟩
    refine ⟨g⁻¹ * δ, k, z, hz, ?_⟩
    change δ • z = modularHyperbolicAxis g hg (t + modularClosedGeodesicPeriod g) at heq
    change (g⁻¹ * δ) • z = modularHyperbolicAxis g hg t
    rw [mul_smul, heq, ← modularHyperbolicAxis_action, inv_smul_smul]
  · rintro ⟨δ, k, z, hz, heq⟩
    refine ⟨g * δ, k, z, hz, ?_⟩
    change δ • z = modularHyperbolicAxis g hg t at heq
    change (g * δ) • z = modularHyperbolicAxis g hg (t + modularClosedGeodesicPeriod g)
    rw [mul_smul, heq, modularHyperbolicAxis_action]

/-- An actual positive-period interval can be based at a phase with BOTH
endpoints off every translated original side. -/
theorem paperAxisSideCuts_exists_period_base_off
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    ∃ a ∈ Ioo 0 (modularClosedGeodesicPeriod g),
      a ∉ paperAxisSideCuts g hg ∧
        a + modularClosedGeodesicPeriod g ∉ paperAxisSideCuts g hg := by
  obtain ⟨a, ha, hoff⟩ := modularHyperbolicAxis_exists_phase_off_paper_sides
    g hg 0 (modularClosedGeodesicPeriod g) (modularClosedGeodesicPeriod_pos g hg)
  have hbase : a ∉ paperAxisSideCuts g hg := by
    rintro ⟨δ, k, hk⟩
    exact hoff δ k hk
  exact ⟨a, ha, hbase, fun h => hbase ((paperAxisSideCuts_period_iff g hg a).mp h)⟩

end Markov
