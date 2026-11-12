import Markov.OrientedPlaneCoordinates
import Markov.TraceProjectedMollifier
import Markov.TraceFourierConvolution

/-! The Fourier slice identity for the normal projection of an integrable
plane function, with the standard Euclidean and one-dimensional measures. -/

noncomputable section
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace
namespace Markov

/-- Integrating a plane function along the transverse line at normal coordinate `t`. -/
def normalProjection (f : EuclideanSpace ℝ (Fin 2) → ℂ)
    (θ : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : ℂ :=
  ∫ s : ℝ, f (t • θ + s • quarterTurnNormal θ)

theorem normalProjection_integrable
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} {θ : EuclideanSpace ℝ (Fin 2)}
    (hθ : ‖θ‖ = 1) (hf : Integrable f) : Integrable (normalProjection f θ) := by
  have hi : Integrable (fun p : ℝ × ℝ ↦ f (orientedPlaneCoordinates θ hθ p)) :=
    ((orientedPlaneCoordinates_measurePreserving θ hθ).integrable_comp_emb
      (orientedPlaneCoordinates θ hθ).measurableEmbedding).mpr hf
  simpa only [normalProjection, orientedPlaneCoordinates_apply] using hi.integral_prod_left

/-- Fourier transformation of a normal projection is restriction of the plane
Fourier transform to that normal line. Only integrability is required. -/
theorem normalProjection_fourier
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} {θ : EuclideanSpace ℝ (Fin 2)}
    (hθ : ‖θ‖ = 1) (hf : Integrable f) (r : ℝ) :
    𝓕 (normalProjection f θ) r = 𝓕 f (r • θ) := by
  let H : EuclideanSpace ℝ (Fin 2) → ℂ := fun z ↦
    Real.fourierChar (-⟪z, r • θ⟫) • f z
  have hHi : Integrable H := (Real.fourierIntegral_convergent_iff (r • θ)).mpr hf
  rw [Real.fourier_real_eq, Real.fourier_eq]
  change (∫ t : ℝ, Real.fourierChar (-(t * r)) • normalProjection f θ t) = ∫ z, H z
  rw [integral_orientedPlaneCoordinates_double θ hθ H hHi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp only [normalProjection, Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  have hphase : inner ℝ (t • θ + s • quarterTurnNormal θ) (r • θ) = r * t := by
    simpa only [orientedPlaneCoordinates_apply] using
      orientedPlaneCoordinates_inner_smul_normal θ hθ (t, s) r
  dsimp only [H]
  rw [hphase, Circle.smul_def, smul_eq_mul]
  rw [mul_comm t r]

/-- Projection commutes exactly with the real-to-complex inclusion. -/
theorem normalProjection_ofReal (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (θ : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    normalProjection (fun z ↦ (f z : ℂ)) θ t =
      ((∫ s : ℝ, f (t • θ + s • quarterTurnNormal θ) : ℝ) : ℂ) := by
  unfold normalProjection
  exact integral_complex_ofReal

/-- The complex projection of the actual scaled mollifier is the already
constructed real projected kernel. -/
theorem normalProjection_traceComplexScaledMollifier (Q : ℝ)
    (θ : EuclideanSpace ℝ (Fin 2)) :
    normalProjection (traceComplexScaledMollifier Q) θ =
      fun t ↦ (traceProjectedMollifier Q θ t : ℂ) := by
  funext t
  exact normalProjection_ofReal (traceScaledMollifier Q) θ t

/-- The actual projected smoothing kernel has exactly the expected Fourier factor. -/
theorem traceProjectedMollifier_fourier (Q : ℝ) (hQ : 0 < Q)
    (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1) (r : ℝ) :
    𝓕 (fun t ↦ (traceProjectedMollifier Q θ t : ℂ)) r =
      𝓕 (traceComplexScaledMollifier Q) (r • θ) := by
  rw [← normalProjection_traceComplexScaledMollifier]
  exact normalProjection_fourier hθ (traceComplexScaledMollifier_integrable Q hQ) r

end Markov
