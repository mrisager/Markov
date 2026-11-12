import Markov.TraceProjectedMollifier
import Markov.TraceSectionFourier
import Markov.TraceSectionConcavity
import Markov.TraceFourierScaling
import Markov.NormalProjectionFourier

/-! The actual one-dimensional smoothing of a perpendicular section profile.
Its kernel is the normal projection of `ρ_(SQ)`, so its Fourier frequencies
are exactly those needed by the complete directional block. -/

noncomputable section
open Set MeasureTheory Function FourierTransform
open scoped Convolution RealInnerProductSpace
namespace Markov

theorem traceSectionProfile_hasCompactSupport {θ : EuclideanSpace ℝ (Fin 2)}
    (hθ : ‖θ‖ = 1) : HasCompactSupport (traceSectionProfile θ) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact
    (Icc (-traceEuclideanSupportHeight (-θ)) (traceEuclideanSupportHeight θ)))
  intro t ht
  exact traceSectionProfile_eq_zero_of_outside_support hθ ht

/-- The actual smoothed section, with projected plane kernel at scale `SQ`. -/
def traceSmoothedSection (S Q : ℝ) (θ : EuclideanSpace ℝ (Fin 2)) : ℝ → ℝ :=
  traceProjectedMollifier (S * Q) θ ⋆ traceSectionProfile θ

theorem traceSmoothedSection_apply (S Q : ℝ) (θ : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    traceSmoothedSection S Q θ t =
      ∫ u : ℝ, traceProjectedMollifier (S * Q) θ u * traceSectionProfile θ (t - u) := rfl

theorem traceSmoothedSection_nonneg (S Q : ℝ) (θ : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    0 ≤ traceSmoothedSection S Q θ t :=
  integral_nonneg (fun u => mul_nonneg (traceProjectedMollifier_nonneg _ θ u)
    (traceSectionProfile_nonneg θ _))

theorem traceSmoothedSection_continuous (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q)
    {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) :
    Continuous (traceSmoothedSection S Q θ) :=
  (traceProjectedMollifier_hasCompactSupport (S * Q) (mul_pos hS hQ) θ hθ).continuous_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (traceProjectedMollifier_continuous (S * Q) (mul_pos hS hQ) θ hθ)
    (traceSectionProfile_integrable hθ).locallyIntegrable

theorem traceSmoothedSection_hasCompactSupport (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q)
    {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) :
    HasCompactSupport (traceSmoothedSection S Q θ) :=
  (traceProjectedMollifier_hasCompactSupport (S * Q) (mul_pos hS hQ) θ hθ).convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) (traceSectionProfile_hasCompactSupport hθ)

theorem traceSmoothedSection_integrable (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q)
    {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) :
    Integrable (traceSmoothedSection S Q θ) :=
  (traceProjectedMollifier_integrable (S * Q) (mul_pos hS hQ) θ hθ).integrable_convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) (traceSectionProfile_integrable hθ)

theorem traceSmoothedSection_integral (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q)
    {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) :
    ∫ t : ℝ, traceSmoothedSection S Q θ t = traceEuclideanArea := by
  rw [traceSmoothedSection, integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ)
    (traceProjectedMollifier_integrable (S * Q) (mul_pos hS hQ) θ hθ)
    (traceSectionProfile_integrable hθ),
    traceProjectedMollifier_integral (S * Q) (mul_pos hS hQ) θ hθ,
    traceSectionProfile_integral hθ]
  simp

/-- The projected convolution is exactly averaging the actual section
profile against the original plane mollifier. -/
theorem traceSmoothedSection_eq_plane_integral (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q)
    {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) (t : ℝ) :
    traceSmoothedSection S Q θ t =
      ∫ y : EuclideanSpace ℝ (Fin 2),
        traceScaledMollifier (S * Q) y * traceSectionProfile θ (t - inner ℝ y θ) := by
  let H : EuclideanSpace ℝ (Fin 2) → ℝ := fun y =>
    traceScaledMollifier (S * Q) y * traceSectionProfile θ (t - inner ℝ y θ)
  have hc : Continuous H := (traceScaledMollifier_contDiff (S * Q)).continuous.mul
    ((continuous_traceSectionProfile hθ).comp
      (continuous_const.sub (continuous_id.inner continuous_const)))
  have hs : HasCompactSupport H :=
    (traceScaledMollifier_hasCompactSupport (S * Q) (mul_pos hS hQ)).mul_right
  have hi : Integrable H := hc.integrable_of_hasCompactSupport hs
  rw [traceSmoothedSection_apply, integral_orientedPlaneCoordinates_double θ hθ H hi]
  apply integral_congr_ae
  filter_upwards with u
  have hp (s : ℝ) : inner ℝ (u • θ + s • quarterTurnNormal θ) θ = u := by
    simpa only [orientedPlaneCoordinates_apply] using orientedPlaneCoordinates_inner_normal θ hθ (u, s)
  simp only [H, hp, traceProjectedMollifier]
  exact (integral_mul_const _ _).symm

theorem traceSmoothedSection_complex_eq (S Q : ℝ) (θ : EuclideanSpace ℝ (Fin 2)) :
    (fun t => (traceSmoothedSection S Q θ t : ℂ)) =
      (fun t => (traceProjectedMollifier (S * Q) θ t : ℂ))
        ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (fun t => (traceSectionProfile θ t : ℂ)) := by
  funext t
  rw [traceSmoothedSection_apply, convolution_mul, ← integral_complex_ofReal]
  congr 1
  funext u
  simp only [Complex.ofReal_mul]

/-- The actual smoothed section has the two expected normal Fourier factors. -/
theorem traceSmoothedSection_fourier_product (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q)
    {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) (r : ℝ) :
    𝓕 (fun t => (traceSmoothedSection S Q θ t : ℂ)) r =
      𝓕 (traceComplexBallIndicator 1) (r • θ) *
        𝓕 (traceComplexScaledMollifier (S * Q)) (r • θ) := by
  rw [traceSmoothedSection_complex_eq]
  calc
    _ = 𝓕 (fun t => (traceProjectedMollifier (S * Q) θ t : ℂ)) r *
        𝓕 (fun t => (traceSectionProfile θ t : ℂ)) r := by
      exact l1_fourier_convolution _ _
        (traceProjectedMollifier_integrable (S * Q) (mul_pos hS hQ) θ hθ).ofReal
        (traceSectionProfile_integrable hθ).ofReal r
    _ = _ := by
      rw [traceProjectedMollifier_fourier (S * Q) (mul_pos hS hQ) θ hθ,
        traceSectionProfile_fourier hθ, mul_comm]

theorem traceSmoothedSection_fourier (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q)
    {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) (r : ℝ) :
    𝓕 (fun t => (traceSmoothedSection S Q θ t : ℂ)) r =
      𝓕 (traceComplexBallIndicator 1) (r • θ) *
        𝓕 traceComplexMollifier ((S * Q)⁻¹ • (r • θ)) := by
  rw [traceSmoothedSection_fourier_product S Q hS hQ hθ,
    trace_mollifier_fourier_scaling (S * Q) (mul_pos hS hQ)]

/-- At the inverse radial mesh, the Fourier factors are exactly the complete
collinear block factors, with no extra power of `S` in the kernel frequency. -/
theorem traceSmoothedSection_fourier_at_ray
    (S Q m : ℝ) (hS : 0 < S) (hQ : 0 < Q)
    (k : EuclideanSpace ℝ (Fin 2)) (hk : k ≠ 0) :
    𝓕 (fun t => (traceSmoothedSection S Q (NormedSpace.normalize k) t : ℂ))
        (m / (S * ‖k‖)⁻¹) =
      𝓕 (traceComplexBallIndicator 1) ((S * m) • k) *
        𝓕 traceComplexMollifier ((m / Q) • k) := by
  have hθ : ‖NormedSpace.normalize k‖ = 1 := NormedSpace.norm_normalize hk
  have hkn : ‖k‖ ≠ 0 := norm_ne_zero_iff.mpr hk
  have hfreq : (m / (S * ‖k‖)⁻¹) • NormedSpace.normalize k = (S * m) • k := by
    rw [NormedSpace.normalize, smul_smul]
    congr 1
    field_simp
  rw [traceSmoothedSection_fourier_product S Q hS hQ hθ, hfreq,
    trace_mollifier_fourier_scaling_at_scaled_frequency S Q m hS hQ k]

end Markov
