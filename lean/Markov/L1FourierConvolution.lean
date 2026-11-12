import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-! The convolution identity for integrable complex functions, including
discontinuous indicators. No continuity hypothesis is imposed. -/

noncomputable section
open MeasureTheory FourierTransform
open scoped Convolution RealInnerProductSpace
namespace Markov

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem fourier_modulation_convolution (f g : V → ℂ) (w x : V) :
    Real.fourierChar (-⟪x, w⟫) •
        (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x =
      ((fun y => Real.fourierChar (-⟪y, w⟫) • f y)
        ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun y => Real.fourierChar (-⟪y, w⟫) • g y)) x := by
  simp only [convolution_mul, Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  have hc : Real.fourierChar (-⟪x, w⟫) =
      Real.fourierChar (-⟪y, w⟫) * Real.fourierChar (-⟪x - y, w⟫) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    rw [inner_sub_left]
    ring
  rw [hc, Circle.coe_mul]
  ring

theorem l1_fourier_convolution (f g : V → ℂ) (hf : Integrable f)
    (hg : Integrable g) (w : V) :
    𝓕 (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) w = 𝓕 f w * 𝓕 g w := by
  rw [Real.fourier_eq]
  simp_rw [fourier_modulation_convolution]
  have hmf := (Real.fourierIntegral_convergent_iff w).mpr hf
  have hmg := (Real.fourierIntegral_convergent_iff w).mpr hg
  exact integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hmf hmg

theorem fourier_comp_positive_smul_plane
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) (R : ℝ) (hR : 0 < R)
    (w : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (fun x => f (R • x)) w = (R ^ 2)⁻¹ • 𝓕 f (R⁻¹ • w) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have hi (x : EuclideanSpace ℝ (Fin 2)) :
      ⟪R • x, R⁻¹ • w⟫ = ⟪x, w⟫ := by
    simp only [real_inner_smul_left, inner_smul_right]
    field_simp
  calc
    (∫ x, Real.fourierChar (-⟪x, w⟫) • f (R • x)) =
        ∫ x, Real.fourierChar (-⟪R • x, R⁻¹ • w⟫) • f (R • x) := by
      simp_rw [hi]
    _ = _ := by
      simpa only [finrank_euclideanSpace_fin] using
        (Measure.integral_comp_smul_of_nonneg volume
          (fun x => Real.fourierChar (-⟪x, R⁻¹ • w⟫) • f x) R (hR := hR.le))

end Markov
