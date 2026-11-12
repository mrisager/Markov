import Markov.TraceRadialPoisson
import Markov.FourierPositivePairs
import Markov.TraceSmoothedSectionSampling
import Markov.TraceRadialScale

/-! The complete positive-frequency block in v1 Lemma 10. Pairing the
absolutely convergent even integer series preserves collinear cancellation. -/

noncomputable section
open MeasureTheory FourierTransform
namespace Markov

def traceRadialBlock (S Q : ℝ) (k : ℤ × ℤ) : ℂ :=
  ((S ^ 2 : ℝ) : ℂ) * ∑' m : ℕ, traceRadialFourierTerm S Q k ((m : ℤ) + 1)

theorem traceSmoothedSection_even (S Q : ℝ) (θ : EuclideanSpace ℝ (Fin 2)) :
    Function.Even (traceSmoothedSection S Q θ) :=
  convolution_even_real (traceProjectedMollifier_even (S * Q) θ) (traceSectionProfile_even θ)

theorem traceRadialFourierTerm_even (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q)
    (k : ℤ × ℤ) (hk : k ≠ 0) : Function.Even (traceRadialFourierTerm S Q k) := by
  have hg : Function.Even (fun t => (traceSmoothedSection S Q (traceRadialNormal k) t : ℂ)) := by
    intro t
    exact congrArg Complex.ofReal (traceSmoothedSection_even S Q (traceRadialNormal k) t)
  intro m
  rw [← traceSmoothedSection_radial_fourier S Q hS hQ k hk (-m),
    ← traceSmoothedSection_radial_fourier S Q hS hQ k hk m]
  simpa only [Int.cast_neg, neg_div] using fourier_even_of_even hg ((m : ℝ) / traceRadialMesh S k)

theorem traceRadialFourierTerm_zero (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q)
    (k : ℤ × ℤ) (hk : k ≠ 0) : traceRadialFourierTerm S Q k 0 = (traceEuclideanArea : ℂ) := by
  rw [← traceSmoothedSection_radial_fourier S Q hS hQ k hk 0]
  simp only [Int.cast_zero, zero_div]
  rw [Real.fourier_eq]
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
  rw [integral_complex_ofReal, traceSmoothedSection_integral S Q hS hQ
    (traceRadialNormal_norm k hk)]

theorem traceRadialBlock_eq_discrepancy (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q)
    (k : ℤ × ℤ) (hk : k ≠ 0) :
    traceRadialBlock S Q k = ((S ^ 2 / 2 : ℝ) : ℂ) *
      ((traceRadialMesh S k * (∑' n : ℤ, traceSmoothedSection S Q (traceRadialNormal k)
        (traceRadialMesh S k * n)) - traceEuclideanArea : ℝ) : ℂ) := by
  have hp := trace_radial_poisson S Q hS hQ k hk
  rw [← Complex.ofReal_tsum] at hp
  simp only [Complex.real_smul] at hp
  rw [← Complex.ofReal_mul] at hp
  have hpair := tsum_int_even_sub_zero_eq_two_mul_tsum_positive
    (traceRadialFourierTerm_norm_summable S Q hQ k hk)
    (traceRadialFourierTerm_even S Q hS hQ k hk)
  rw [traceRadialFourierTerm_zero S Q hS hQ k hk] at hpair
  have hd : ((traceRadialMesh S k *
      (∑' n : ℤ, traceSmoothedSection S Q (traceRadialNormal k) (traceRadialMesh S k * n)) -
      traceEuclideanArea : ℝ) : ℂ) =
      2 * ∑' m : ℕ, traceRadialFourierTerm S Q k ((m : ℤ) + 1) := by
    rw [Complex.ofReal_sub, hp]
    exact hpair
  rw [hd, traceRadialBlock]
  push_cast
  ring

theorem trace_lemma10_first (S Q : ℝ)
    (hS : 8 / traceEuclideanInradius + 1 ≤ S) (hQ : 0 < Q)
    (k : ℤ × ℤ) (hk : k ≠ 0) :
    ‖traceRadialBlock S Q k‖ ≤ (7 * S / ‖euclideanIntDirection k‖) *
      Metric.diam (traceConvexCap (traceRadialNormal k) (traceRadialMesh S k)) := by
  have hSp := trace_radial_scale_pos_of_threshold hS
  have hθ := traceRadialNormal_norm k hk
  have hstep := trace_radial_sampling_step_bounds hθ hk hS
  have hs := traceSmoothedSection_sampling_cap_bound S Q hSp hQ hθ hstep.1 hstep.2
  have hcoef : 0 ≤ S ^ 2 / 2 := div_nonneg (sq_nonneg S) (by norm_num)
  calc
    _ = (S ^ 2 / 2) * |traceRadialMesh S k *
        (∑' n : ℤ, traceSmoothedSection S Q (traceRadialNormal k) (traceRadialMesh S k * n)) -
        traceEuclideanArea| := by
      rw [traceRadialBlock_eq_discrepancy S Q hSp hQ k hk, norm_mul]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef]
    _ ≤ (S ^ 2 / 2) * (14 * traceRadialMesh S k *
        Metric.diam (traceConvexCap (traceRadialNormal k) (traceRadialMesh S k))) :=
      mul_le_mul_of_nonneg_left hs hcoef
    _ = _ := by
      unfold traceRadialMesh
      field_simp
      ring

end Markov
