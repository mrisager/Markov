import Markov.TracePoisson

/-! The actual full trace-lattice discrepancy reduced to the two nonzero
Fourier sums, with the smoothing main-term error made explicit. -/

noncomputable section
namespace Markov

def traceFourierError (R Q : ℝ) : ℝ :=
  ∑' n : {n : ℤ × ℤ // n ≠ 0}, ‖traceFourierLatticeTerm R Q n‖

theorem traceFourierError_nonneg (R Q : ℝ) : 0 ≤ traceFourierError R Q :=
  tsum_nonneg (fun _ => norm_nonneg _)

theorem smoothing_quadratic_mainterm_bounds (A R e : ℝ)
    (hA : 0 ≤ A) (he : 0 ≤ e) (hR : e ≤ R) :
    |(R - e) ^ 2 * A - R ^ 2 * A| ≤ 3 * A * R * e ∧
      |(R + e) ^ 2 * A - R ^ 2 * A| ≤ 3 * A * R * e := by
  have hRe : 0 ≤ R := he.trans hR
  have h1 : 0 ≤ A * e * (R - e) :=
    mul_nonneg (mul_nonneg hA he) (sub_nonneg.mpr hR)
  have h2 : 0 ≤ A * R * e := mul_nonneg (mul_nonneg hA hRe) he
  have h3 : 0 ≤ A * e ^ 2 := mul_nonneg hA (sq_nonneg e)
  constructor <;> apply abs_le.mpr <;> constructor <;> nlinarith

theorem trace_lattice_discrepancy_fourier_bound (R Q : ℝ) (hQ : 0 < Q)
    (hR : 0 < R - traceEuclideanGaugeConstant / Q) :
    |(traceLatticeCount R : ℝ) - R ^ 2 * traceEuclideanArea| ≤
      3 * traceEuclideanArea * R * (traceEuclideanGaugeConstant / Q) +
        max (traceFourierError (R - traceEuclideanGaugeConstant / Q) Q)
          (traceFourierError (R + traceEuclideanGaugeConstant / Q) Q) := by
  let e := traceEuclideanGaugeConstant / Q
  have he : 0 < e := div_pos traceEuclideanGaugeConstant_pos hQ
  have hRp : 0 < R := by linarith
  have hplus : 0 < R + e := by linarith
  have hsand := traceSmoothingSandwich_latticeCount R Q hQ hR
  have hminus := trace_smoothed_lattice_discrepancy_le (R - e) Q hR hQ
  have hpluserr := trace_smoothed_lattice_discrepancy_le (R + e) Q hplus hQ
  change |traceSmoothedLatticeCount (R - e) Q - (R - e) ^ 2 * traceEuclideanArea| ≤
    traceFourierError (R - e) Q at hminus
  change |traceSmoothedLatticeCount (R + e) Q - (R + e) ^ 2 * traceEuclideanArea| ≤
    traceFourierError (R + e) Q at hpluserr
  have hmain := smoothing_quadratic_mainterm_bounds traceEuclideanArea R e
    traceEuclideanArea_pos.le he.le (by linarith)
  have hlow := (abs_le.mp hminus).1
  have hhigh := (abs_le.mp hpluserr).2
  have hlowmain := (abs_le.mp hmain.1).1
  have hhighmain := (abs_le.mp hmain.2).2
  have hEminus := le_max_left (traceFourierError (R - e) Q) (traceFourierError (R + e) Q)
  have hEplus := le_max_right (traceFourierError (R - e) Q) (traceFourierError (R + e) Q)
  change |(traceLatticeCount R : ℝ) - R ^ 2 * traceEuclideanArea| ≤
    3 * traceEuclideanArea * R * e + max (traceFourierError (R - e) Q)
      (traceFourierError (R + e) Q)
  change traceSmoothedLatticeCount (R - e) Q ≤ (traceLatticeCount R : ℝ) ∧
    (traceLatticeCount R : ℝ) ≤ traceSmoothedLatticeCount (R + e) Q at hsand
  apply abs_le.mpr
  constructor <;> linarith [hsand.1, hsand.2]

end Markov
