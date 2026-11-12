import Markov.TraceSmoothingSandwich
import Markov.L1FourierConvolution

/-! The actual trace-ball indicator is integrable although discontinuous.
The Fourier product formula below therefore uses the L¹ bridge. -/

noncomputable section
open Set MeasureTheory FourierTransform
open scoped Pointwise Convolution ContDiff
open scoped RealInnerProductSpace
namespace Markov

def traceComplexBallIndicator (R : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  (R • traceEuclideanBall).indicator (fun _ => 1) x

theorem traceComplexBallIndicator_eq (R : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    traceComplexBallIndicator R x = (traceBallIndicator R x : ℂ) := by
  classical
  by_cases hx : x ∈ R • traceEuclideanBall <;>
    simp [traceComplexBallIndicator, traceBallIndicator, hx]

theorem traceComplexBallIndicator_integrable (R : ℝ) :
    Integrable (traceComplexBallIndicator R) := by
  have hi : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℂ))
      (R • traceEuclideanBall) :=
    integrableOn_const (isCompact_smul_traceEuclideanBall R).measure_lt_top.ne
  exact hi.integrable_indicator (isCompact_smul_traceEuclideanBall R).measurableSet

def traceComplexScaledMollifier (Q : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  (traceScaledMollifier Q x : ℂ)

theorem traceComplexScaledMollifier_integrable (Q : ℝ) (hQ : 0 < Q) :
    Integrable (traceComplexScaledMollifier Q) :=
  (traceScaledMollifier_integrable Q hQ).ofReal

theorem traceComplexScaledMollifier_integral (Q : ℝ) (hQ : 0 < Q) :
    ∫ x, traceComplexScaledMollifier Q x = 1 := by
  unfold traceComplexScaledMollifier
  rw [integral_complex_ofReal, traceScaledMollifier_integral Q hQ]
  norm_num

theorem trace_indicator_mollifier_fourier (R Q : ℝ) (hQ : 0 < Q)
    (w : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (traceComplexBallIndicator R ⋆[ContinuousLinearMap.mul ℂ ℂ]
      traceComplexScaledMollifier Q) w =
      𝓕 (traceComplexBallIndicator R) w * 𝓕 (traceComplexScaledMollifier Q) w :=
  l1_fourier_convolution _ _ (traceComplexBallIndicator_integrable R)
    (traceComplexScaledMollifier_integrable Q hQ) w

theorem traceComplexSmoothedIndicator_eq (R Q : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (traceSmoothedIndicator R Q x : ℂ) =
      (traceComplexScaledMollifier Q ⋆[ContinuousLinearMap.mul ℂ ℂ]
        traceComplexBallIndicator R) x := by
  rw [traceSmoothedIndicator_apply, convolution_mul, ← integral_complex_ofReal]
  congr 1
  funext y
  simp only [traceComplexScaledMollifier, traceComplexBallIndicator_eq,
    Complex.ofReal_mul]

theorem trace_smoothed_indicator_fourier (R Q : ℝ) (hQ : 0 < Q)
    (w : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (fun x => (traceSmoothedIndicator R Q x : ℂ)) w =
      𝓕 (traceComplexBallIndicator R) w * 𝓕 (traceComplexScaledMollifier Q) w := by
  simp_rw [traceComplexSmoothedIndicator_eq]
  rw [l1_fourier_convolution _ _ (traceComplexScaledMollifier_integrable Q hQ)
    (traceComplexBallIndicator_integrable R), mul_comm]

theorem traceEuclideanBall_dilate_volume (R : ℝ) :
    volume (R • traceEuclideanBall) = ENNReal.ofReal (R ^ 2) * volume traceEuclideanBall := by
  rw [Measure.addHaar_smul]
  simp only [finrank_euclideanSpace_fin, abs_of_nonneg (sq_nonneg R)]

theorem traceBallIndicator_integral (R : ℝ) :
    ∫ x, traceBallIndicator R x = R ^ 2 * traceEuclideanArea := by
  rw [traceBallIndicator, integral_indicator (measurableSet_smul_traceEuclideanBall R),
    integral_const, Measure.real, Measure.restrict_apply_univ, traceEuclideanBall_dilate_volume,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg R)]
  simp only [smul_eq_mul, mul_one, traceEuclideanArea]

theorem traceSmoothedIndicator_integral (R Q : ℝ) (hQ : 0 < Q) :
    ∫ x, traceSmoothedIndicator R Q x = R ^ 2 * traceEuclideanArea := by
  rw [traceSmoothedIndicator, integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ)
    (traceScaledMollifier_integrable Q hQ) (traceBallIndicator_integrable R),
    traceScaledMollifier_integral Q hQ, traceBallIndicator_integral]
  simp

theorem traceSmoothedIndicator_fourier_zero (R Q : ℝ) (hQ : 0 < Q) :
    𝓕 (fun x => (traceSmoothedIndicator R Q x : ℂ)) 0 =
      (R ^ 2 * traceEuclideanArea : ℝ) := by
  rw [Real.fourier_eq]
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
  rw [integral_complex_ofReal, traceSmoothedIndicator_integral R Q hQ]

theorem traceComplexSmoothedIndicator_hasCompactSupport (R Q : ℝ) (hQ : 0 < Q) :
    HasCompactSupport (fun x => (traceSmoothedIndicator R Q x : ℂ)) := by
  simpa [HasCompactSupport, tsupport, Function.support] using
    traceSmoothedIndicator_hasCompactSupport R Q hQ

theorem traceComplexSmoothedIndicator_contDiff (R Q : ℝ) (hQ : 0 < Q) :
    ContDiff ℝ ∞ (fun x => (traceSmoothedIndicator R Q x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (traceSmoothedIndicator_contDiff R Q hQ)

/-- The smoothed indicator as a Schwartz function for
two-dimensional lattice Poisson summation. -/
def traceSmoothedSchwartz (R Q : ℝ) (hQ : 0 < Q) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  (traceComplexSmoothedIndicator_hasCompactSupport R Q hQ).toSchwartzMap
    (traceComplexSmoothedIndicator_contDiff R Q hQ)

@[simp] theorem traceSmoothedSchwartz_apply (R Q : ℝ) (hQ : 0 < Q)
    (x : EuclideanSpace ℝ (Fin 2)) :
    traceSmoothedSchwartz R Q hQ x = (traceSmoothedIndicator R Q x : ℂ) := rfl

end Markov
