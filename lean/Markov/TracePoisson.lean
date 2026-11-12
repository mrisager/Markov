import Markov.PoissonPlane
import Markov.TraceFourierScaling

/-! The exact two-dimensional Poisson identity for the actual smoothed
trace-ball lattice count, with the proved Fourier normalization. -/

noncomputable section
open MeasureTheory FourierTransform
namespace Markov

theorem trace_smoothed_fourier_lattice_norm_summable (R Q : ℝ) (hQ : 0 < Q) :
    Summable (fun n : ℤ × ℤ =>
      ‖𝓕 (fun x => (traceSmoothedIndicator R Q x : ℂ)) (euclideanIntDirection n)‖) :=
  schwartz_fourier_lattice_norm_summable (traceSmoothedSchwartz R Q hQ)

theorem trace_smoothed_fourier_lattice_summable (R Q : ℝ) (hQ : 0 < Q) :
    Summable (fun n : ℤ × ℤ =>
      𝓕 (fun x => (traceSmoothedIndicator R Q x : ℂ)) (euclideanIntDirection n)) :=
  (trace_smoothed_fourier_lattice_norm_summable R Q hQ).of_norm

theorem trace_smoothed_lattice_poisson (R Q : ℝ) (hR : 0 < R) (hQ : 0 < Q) :
    (traceSmoothedLatticeCount R Q : ℂ) =
      ∑' n : ℤ × ℤ, 𝓕 (fun x => (traceSmoothedIndicator R Q x : ℂ))
        (euclideanIntDirection n) := by
  rw [traceSmoothedLatticeCount_eq_tsum R Q hR hQ, Complex.ofReal_tsum]
  exact compact_schwartz_plane_poisson (traceSmoothedSchwartz R Q hQ)
    (traceComplexSmoothedIndicator_hasCompactSupport R Q hQ)

def traceFourierLatticeTerm (R Q : ℝ) (n : ℤ × ℤ) : ℂ :=
  ((R ^ 2 : ℝ) : ℂ) * 𝓕 (traceComplexBallIndicator 1) (R • euclideanIntDirection n) *
    𝓕 traceComplexMollifier (Q⁻¹ • euclideanIntDirection n)

theorem traceFourierLatticeTerm_eq (R Q : ℝ) (hR : 0 < R) (hQ : 0 < Q)
    (n : ℤ × ℤ) :
    traceFourierLatticeTerm R Q n =
      𝓕 (fun x => (traceSmoothedIndicator R Q x : ℂ)) (euclideanIntDirection n) :=
  (trace_smoothed_indicator_fourier_scaling R Q hR hQ _).symm

theorem traceFourierLatticeTerm_norm_summable (R Q : ℝ) (hR : 0 < R) (hQ : 0 < Q) :
    Summable (fun n : ℤ × ℤ => ‖traceFourierLatticeTerm R Q n‖) := by
  simp_rw [traceFourierLatticeTerm_eq R Q hR hQ]
  exact trace_smoothed_fourier_lattice_norm_summable R Q hQ

theorem trace_smoothed_lattice_fourier_expansion (R Q : ℝ) (hR : 0 < R) (hQ : 0 < Q) :
    (traceSmoothedLatticeCount R Q : ℂ) = ∑' n : ℤ × ℤ, traceFourierLatticeTerm R Q n := by
  simp_rw [traceFourierLatticeTerm_eq R Q hR hQ]
  exact trace_smoothed_lattice_poisson R Q hR hQ

theorem traceFourierLatticeTerm_zero (R Q : ℝ) (hR : 0 < R) (hQ : 0 < Q) :
    traceFourierLatticeTerm R Q 0 = (R ^ 2 * traceEuclideanArea : ℝ) := by
  rw [traceFourierLatticeTerm_eq R Q hR hQ]
  have hzero : euclideanIntDirection (0 : ℤ × ℤ) = 0 := by
    ext i
    fin_cases i <;> simp [euclideanIntDirection]
  rw [hzero, traceSmoothedIndicator_fourier_zero R Q hQ]

theorem trace_smoothed_lattice_poisson_nonzero (R Q : ℝ) (hR : 0 < R) (hQ : 0 < Q) :
    (traceSmoothedLatticeCount R Q : ℂ) = (R ^ 2 * traceEuclideanArea : ℝ) +
      ∑' n : {n : ℤ × ℤ // n ≠ 0}, traceFourierLatticeTerm R Q n := by
  rw [trace_smoothed_lattice_fourier_expansion R Q hR hQ]
  have hs := (traceFourierLatticeTerm_norm_summable R Q hR hQ).of_norm
  have heq := hs.sum_add_tsum_subtype_compl ({0} : Finset (ℤ × ℤ))
  have hpred : (fun n : ℤ × ℤ => n ∉ ({0} : Finset (ℤ × ℤ))) = (fun n => n ≠ 0) := by
    funext n
    apply propext
    simp
  change (∑ n ∈ ({0} : Finset (ℤ × ℤ)), traceFourierLatticeTerm R Q n) +
      (∑' n : {n : ℤ × ℤ // n ∉ ({0} : Finset (ℤ × ℤ))}, traceFourierLatticeTerm R Q n) =
    ∑' n : ℤ × ℤ, traceFourierLatticeTerm R Q n at heq
  rw [hpred] at heq
  simpa only [Finset.sum_singleton, traceFourierLatticeTerm_zero R Q hR hQ] using heq.symm

theorem trace_smoothed_lattice_discrepancy_le (R Q : ℝ) (hR : 0 < R) (hQ : 0 < Q) :
    |traceSmoothedLatticeCount R Q - R ^ 2 * traceEuclideanArea| ≤
      ∑' n : {n : ℤ × ℤ // n ≠ 0}, ‖traceFourierLatticeTerm R Q n‖ := by
  have hid : ((traceSmoothedLatticeCount R Q - R ^ 2 * traceEuclideanArea : ℝ) : ℂ) =
      ∑' n : {n : ℤ × ℤ // n ≠ 0}, traceFourierLatticeTerm R Q n := by
    rw [Complex.ofReal_sub, trace_smoothed_lattice_poisson_nonzero R Q hR hQ]
    ring
  calc
    _ = ‖((traceSmoothedLatticeCount R Q - R ^ 2 * traceEuclideanArea : ℝ) : ℂ)‖ :=
      (Complex.norm_real _).symm
    _ = ‖∑' n : {n : ℤ × ℤ // n ≠ 0}, traceFourierLatticeTerm R Q n‖ := congrArg norm hid
    _ ≤ _ := norm_tsum_le_tsum_norm
      ((traceFourierLatticeTerm_norm_summable R Q hR hQ).subtype {n | n ≠ 0})

end Markov
