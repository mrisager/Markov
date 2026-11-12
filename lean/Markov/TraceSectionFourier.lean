import Markov.TraceSections
import Markov.OrientedPlaneCoordinates
import Markov.TraceFourierConvolution

/-! The actual perpendicular section profile, its Euclidean area and its
Fourier transform along the original normal direction. -/

noncomputable section
open Set MeasureTheory FourierTransform
open scoped Pointwise RealInnerProductSpace
namespace Markov

theorem traceSectionProfile_integrable {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) :
    Integrable (traceSectionProfile θ) := by
  have hi : Integrable (fun p : ℝ × ℝ =>
      traceBallIndicator 1 (orientedPlaneCoordinates θ hθ p)) :=
    ((orientedPlaneCoordinates_measurePreserving θ hθ).integrable_comp_emb
      (orientedPlaneCoordinates θ hθ).measurableEmbedding).mpr (traceBallIndicator_integrable 1)
  simpa only [orientedPlaneCoordinates_apply, traceBallIndicator, one_smul,
    traceSectionProfile, traceSectionPoint] using hi.integral_prod_left

theorem traceSectionProfile_integral {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) :
    (∫ t, traceSectionProfile θ t) = traceEuclideanArea := by
  have hh := integral_orientedPlaneCoordinates_double θ hθ (traceBallIndicator 1)
    (traceBallIndicator_integrable 1)
  have heq : (∫ t, traceSectionProfile θ t) = ∫ z, traceBallIndicator 1 z := by
    simpa only [traceBallIndicator, one_smul, traceSectionProfile, traceSectionPoint] using hh.symm
  rw [heq, traceBallIndicator_integral]
  norm_num

theorem traceSectionProfile_fourier {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1)
    (r : ℝ) :
    𝓕 (fun t => (traceSectionProfile θ t : ℂ)) r =
      𝓕 (traceComplexBallIndicator 1) (r • θ) := by
  let H : EuclideanSpace ℝ (Fin 2) → ℂ := fun z =>
    Real.fourierChar (-⟪z, r • θ⟫) • traceComplexBallIndicator 1 z
  have hi : Integrable H :=
    (Real.fourierIntegral_convergent_iff (r • θ)).mpr (traceComplexBallIndicator_integrable 1)
  rw [Real.fourier_real_eq, Real.fourier_eq]
  change (∫ t : ℝ, Real.fourierChar (-(t * r)) • (traceSectionProfile θ t : ℂ)) = ∫ z, H z
  rw [integral_orientedPlaneCoordinates_double θ hθ H hi]
  apply integral_congr_ae
  filter_upwards with t
  have hp (s : ℝ) : ⟪t • θ + s • quarterTurnNormal θ, r • θ⟫ = r * t := by
    simpa only [orientedPlaneCoordinates_apply, Prod.fst, Prod.snd] using
      orientedPlaneCoordinates_inner_smul_normal θ hθ (t, s) r
  have hc (s : ℝ) : traceComplexBallIndicator 1 (t • θ + s • quarterTurnNormal θ) =
      Complex.ofReal (traceEuclideanBall.indicator (fun _ => (1 : ℝ))
        (t • θ + s • quarterTurnNormal θ)) := by
    rw [traceComplexBallIndicator_eq]
    simp only [traceBallIndicator, one_smul]
  simp only [H, hp, hc, traceSectionProfile, traceSectionPoint]
  rw [← integral_complex_ofReal]
  simp only [Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext s
  rw [mul_comm r t]

end Markov
