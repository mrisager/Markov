import Markov.SmoothedSampling
import Markov.TraceSmoothedSections
import Markov.TraceSectionSampling
import Markov.TraceSectionSymmetry

/-! Averaging the actual section sampling estimate against rho_(SQ),
with the uniform finite window and integral exchange fully justified. -/

noncomputable section
open MeasureTheory
namespace Markov

theorem traceSmoothedSection_sampling_bound (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q)
    {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) {h : ℝ} (hh : 0 < h)
    (hhsmall : h < (traceEuclideanSupportHeight θ + traceEuclideanSupportHeight (-θ)) / 8) :
    Summable (fun n : ℤ => traceSmoothedSection S Q θ (h * n)) ∧
      |h * (∑' n : ℤ, traceSmoothedSection S Q θ (h * n)) - traceEuclideanArea| ≤
        7 * h * (traceSectionProfile θ (-traceEuclideanSupportHeight (-θ) + h) +
          traceSectionProfile θ (traceEuclideanSupportHeight θ - h)) := by
  have hs : ∀ u : ℝ,
      |h * (∑' n : ℤ, traceSectionProfile θ (h * n - u)) -
        ∫ x, traceSectionProfile θ x| ≤
      7 * h * (traceSectionProfile θ (-traceEuclideanSupportHeight (-θ) + h) +
        traceSectionProfile θ (traceEuclideanSupportHeight θ - h)) := by
    intro u
    have ht := (traceSectionProfile_sampling hθ hh hhsmall (-u / h)).2
    have hp (n : ℤ) : h * ((n : ℝ) + -u / h) = h * n - u := by
      field_simp
      ring
    simp_rw [hp] at ht
    simpa only [traceSectionProfile_integral hθ] using ht
  have key := smoothed_sampling_bound (traceSectionProfile θ)
    (traceProjectedMollifier (S * Q) θ) (continuous_traceSectionProfile hθ)
    (traceSectionProfile_hasCompactSupport hθ)
    (traceProjectedMollifier_continuous (S * Q) (mul_pos hS hQ) θ hθ)
    (traceProjectedMollifier_hasCompactSupport (S * Q) (mul_pos hS hQ) θ hθ)
    (traceProjectedMollifier_nonneg (S * Q) θ)
    (traceProjectedMollifier_integral (S * Q) (mul_pos hS hQ) θ hθ) hh hs
  rw [traceSectionProfile_integral hθ] at key
  exact key

theorem traceSmoothedSection_sampling_cap_bound (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q)
    {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) {h : ℝ} (hh : 0 < h)
    (hhsmall : h < (traceEuclideanSupportHeight θ + traceEuclideanSupportHeight (-θ)) / 8) :
    |h * (∑' n : ℤ, traceSmoothedSection S Q θ (h * n)) - traceEuclideanArea| ≤
      14 * h * Metric.diam (traceConvexCap θ h) := by
  have hs := (traceSmoothedSection_sampling_bound S Q hS hQ hθ hh hhsmall).2
  have hl := traceSectionProfile_le_opposite_cap_diam hθ
    (-traceEuclideanSupportHeight (-θ) + h) h (by linarith)
  have hr := traceSectionProfile_le_cap_diam hθ
    (traceEuclideanSupportHeight θ - h) h (by linarith)
  rw [traceConvexCap_diam_neg_normal θ h] at hl
  have hm := mul_le_mul_of_nonneg_left (add_le_add hl hr)
    (show 0 ≤ 7 * h by positivity)
  exact hs.trans (by nlinarith)

end Markov
