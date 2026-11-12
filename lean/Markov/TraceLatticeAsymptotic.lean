import Markov.TraceLatticeSharpParameters
import Markov.TheoremTwelveParameters

/-! The paper's parameter choice gives the full lattice estimate
for the trace norm. `IntrinsicMcShaneRivinCount` transfers the estimate
to the geometric unit ball and the original marked lattice. -/

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace Markov

/-- The exact full-count asymptotic for the constructed trace ball, following
the v1 smoothing, positive-ray, cap, and logarithmic-parameter proof route. -/
theorem trace_lattice_asymptotic :
    (fun R : ℝ => (traceLatticeCount R : ℝ) - traceEuclideanArea * R ^ 2) =O[atTop]
      (fun R : ℝ => R / Real.log R ^ (3 / 2 : ℝ)) := by
  obtain ⟨C, c, H0, hC, hc, _hH0, hb⟩ := trace_lattice_sharp_parameter_bound
  let κ := 2 * traceAxisLength
  have hκ : 0 < κ := mul_pos (by norm_num) traceAxisLength_pos
  let E : ℝ → ℝ := fun R =>
    Real.log (2 * theoremTwelveK R) / theoremTwelveEta R +
      R / (theoremTwelveH κ R * Real.sqrt (theoremTwelveH κ R)) +
      R * theoremTwelveK R * Real.exp (-(c * theoremTwelveH κ R)) +
      R / theoremTwelveQ R + R * theoremTwelveQ R ^ 3 / theoremTwelveK R ^ 2
  have hEO : E =O[atTop] (fun R : ℝ => R / Real.log R ^ (3 / 2 : ℝ)) := by
    simpa only [E, neg_mul] using theoremTwelve_total_error_isBigO κ c hκ hc
  have hadm := theoremTwelve_eventually_admissible κ traceCornerLowerConstant H0
    (8 / traceEuclideanInradius + 1) traceEuclideanGaugeConstant hκ
    traceCornerLowerConstant_pos traceEuclideanGaugeConstant_pos.le
  have hdom : (fun R : ℝ => (traceLatticeCount R : ℝ) - traceEuclideanArea * R ^ 2)
      =O[atTop] E := by
    apply IsBigO.of_bound C
    filter_upwards [hadm] with R hR
    rcases hR with ⟨_hRp, hQone, hQK, hH, hη, hbasic, hS⟩
    have hQ : 0 < theoremTwelveQ R := lt_of_lt_of_le zero_lt_one hQone
    have hK : 1 ≤ theoremTwelveK R := hQone.trans hQK.le
    have hgap : (2 + (1 : ℝ)) * theoremTwelveEta R ≤ traceCornerLowerConstant *
        Real.exp (-(2 * traceAxisLength * theoremTwelveH κ R)) := by
      simpa only [κ, neg_mul, show (2 : ℝ) + 1 = 3 by norm_num] using hbasic
    have hh := hb R (theoremTwelveQ R) (theoremTwelveK R) (theoremTwelveH κ R)
      1 (theoremTwelveEta R) hS hQ hK hH (by norm_num) hη hgap
    have hh' : |(traceLatticeCount R : ℝ) - traceEuclideanArea * R ^ 2| ≤ C * E R := by
      simpa only [E, mul_comm traceEuclideanArea (R ^ 2)] using hh
    simpa only [Real.norm_eq_abs] using hh'.trans
      (mul_le_mul_of_nonneg_left (le_abs_self (E R)) hC.le)
  exact hdom.trans hEO

end Markov
