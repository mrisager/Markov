import Markov.TraceFourierConvolution

/-! Exact two-dimensional Fourier scaling for the actual trace indicator
and the explicit radial mollifier, with standard Euclidean volume and the
`exp(-2π i ⟪x,ξ⟫)` convention. -/

noncomputable section
open Set MeasureTheory FourierTransform
open scoped Pointwise RealInnerProductSpace
namespace Markov

/-- The complex-valued unit-mass radial mollifier. -/
def traceComplexMollifier (x : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  (traceRadialMollifier x : ℂ)

theorem traceComplexMollifier_integrable : Integrable traceComplexMollifier :=
  traceRadialMollifier_integrable.ofReal

theorem fourier_real_const_mul_plane
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) (a : ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (fun x => (a : ℂ) * f x) w = (a : ℂ) * 𝓕 f w := by
  calc
    _ = ∫ x, (a : ℂ) * (Real.fourierChar (-⟪x, w⟫) • f x) := by
      rw [Real.fourier_eq]
      congr 1
      funext x
      simp only [Circle.smul_def, smul_eq_mul]
      ring
    _ = _ := by rw [integral_const_mul, Real.fourier_eq]

theorem traceComplexBallIndicator_dilate (R : ℝ) (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin 2)) :
    traceComplexBallIndicator R x = traceComplexBallIndicator 1 (R⁻¹ • x) := by
  have hm : x ∈ R • traceEuclideanBall ↔ R⁻¹ • x ∈ (1 : ℝ) • traceEuclideanBall := by
    rw [mem_smul_traceEuclideanBall_iff R hR,
      mem_smul_traceEuclideanBall_iff 1 zero_lt_one, traceEuclideanGauge_smul,
      abs_of_pos (inv_pos.mpr hR)]
    constructor
    · intro hx
      exact (mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)).trans_eq
        (inv_mul_cancel₀ hR.ne')
    · intro hx
      have hh := mul_le_mul_of_nonneg_left hx hR.le
      simpa only [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, mul_one] using hh
  classical
  simp only [traceComplexBallIndicator, indicator_apply, hm]

theorem trace_indicator_fourier_scaling (R : ℝ) (hR : 0 < R)
    (w : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (traceComplexBallIndicator R) w =
      (R ^ 2 : ℝ) • 𝓕 (traceComplexBallIndicator 1) (R • w) := by
  have hf : traceComplexBallIndicator R =
      fun x => traceComplexBallIndicator 1 (R⁻¹ • x) :=
    funext (traceComplexBallIndicator_dilate R hR)
  rw [hf, fourier_comp_positive_smul_plane _ R⁻¹ (inv_pos.mpr hR)]
  simp only [inv_pow, inv_inv]

theorem traceComplexScaledMollifier_eq (Q : ℝ) :
    traceComplexScaledMollifier Q =
      fun x => (Q ^ 2 : ℂ) * traceComplexMollifier (Q • x) := by
  funext x
  simp only [traceComplexScaledMollifier, traceScaledMollifier,
    traceComplexMollifier, Complex.ofReal_mul, Complex.ofReal_pow]

theorem trace_mollifier_fourier_scaling (Q : ℝ) (hQ : 0 < Q)
    (w : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (traceComplexScaledMollifier Q) w = 𝓕 traceComplexMollifier (Q⁻¹ • w) := by
  rw [traceComplexScaledMollifier_eq]
  have he : (fun x => (Q ^ 2 : ℂ) * traceComplexMollifier (Q • x)) =
      fun x => ((Q ^ 2 : ℝ) : ℂ) * traceComplexMollifier (Q • x) := by
    simp only [Complex.ofReal_pow]
  rw [he, fourier_real_const_mul_plane,
    fourier_comp_positive_smul_plane _ Q hQ]
  rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (pow_ne_zero _ hQ.ne'), Complex.ofReal_one, one_mul]

/-- The actual smoothed Fourier transform, with both scaling factors explicit. -/
theorem trace_smoothed_indicator_fourier_scaling (R Q : ℝ) (hR : 0 < R) (hQ : 0 < Q)
    (w : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (fun x => (traceSmoothedIndicator R Q x : ℂ)) w =
      ((R ^ 2 : ℝ) : ℂ) * 𝓕 (traceComplexBallIndicator 1) (R • w) *
        𝓕 traceComplexMollifier (Q⁻¹ • w) := by
  rw [trace_smoothed_indicator_fourier R Q hQ,
    trace_indicator_fourier_scaling R hR, trace_mollifier_fourier_scaling Q hQ,
    Complex.real_smul]

/-- The `ρ_(SQ)` factor at frequency `S m k` is exactly `ρ̂(m k/Q)`. -/
theorem trace_mollifier_fourier_scaling_at_scaled_frequency
    (S Q m : ℝ) (hS : 0 < S) (hQ : 0 < Q) (k : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (traceComplexScaledMollifier (S * Q)) ((S * m) • k) =
      𝓕 traceComplexMollifier ((m / Q) • k) := by
  rw [trace_mollifier_fourier_scaling (S * Q) (mul_pos hS hQ), smul_smul]
  field_simp

end Markov
