import Markov.EuclideanPairCoordinates
import Mathlib.Analysis.Fourier.PoissonSummation

/-! The partial Fourier transform of a continuous compactly supported plane
function. Only continuity and compact support are needed before applying the
one-dimensional Poisson theorem; no smooth parameter-integral claim is made. -/

noncomputable section
open Set MeasureTheory Function FourierTransform
open scoped Topology RealInnerProductSpace
namespace Markov

/-- Fourier transformation in the second coordinate, leaving the first spatial
coordinate free. The measure is ordinary one-dimensional Lebesgue measure. -/
def partialFourierPlane (f : EuclideanSpace ℝ (Fin 2) → ℂ) (m x : ℝ) : ℂ :=
  ∫ y : ℝ, Real.fourierChar (-(y * m)) • f (euclideanPairEquiv (x, y))

theorem hasCompactSupport_comp_euclideanPairEquiv
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (f ∘ euclideanPairEquiv) :=
  hf.comp_isClosedEmbedding euclideanPairEquiv_isClosedEmbedding

/-- The same compact projection bounds every partial transform, uniformly in
the Fourier parameter. -/
theorem partialFourierPlane_eq_zero_of_not_mem_fst_tsupport
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) (m x : ℝ)
    (hx : x ∉ Prod.fst '' tsupport (f ∘ euclideanPairEquiv)) :
    partialFourierPlane f m x = 0 := by
  unfold partialFourierPlane
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro y
  change Real.fourierChar (-(y * m)) • f (euclideanPairEquiv (x, y)) = 0
  have hzero : f (euclideanPairEquiv (x, y)) = 0 := by
    by_contra hh
    apply hx
    exact ⟨(x, y), subset_closure (show (x, y) ∈ support (f ∘ euclideanPairEquiv) from hh), rfl⟩
  rw [hzero, smul_zero]

theorem partialFourierPlane_hasCompactSupport
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : HasCompactSupport f) (m : ℝ) :
    HasCompactSupport (partialFourierPlane f m) := by
  apply HasCompactSupport.intro
    ((hasCompactSupport_comp_euclideanPairEquiv hf).isCompact.image continuous_fst)
  exact partialFourierPlane_eq_zero_of_not_mem_fst_tsupport f m

theorem partialFourierPlane_continuous
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hc : Continuous f)
    (hf : HasCompactSupport f) (m : ℝ) : Continuous (partialFourierPlane f m) := by
  have hF : Continuous (f ∘ euclideanPairEquiv) := hc.comp euclideanPairEquiv_continuous
  have hK : IsCompact (Prod.snd '' tsupport (f ∘ euclideanPairEquiv)) :=
    (hasCompactSupport_comp_euclideanPairEquiv hf).isCompact.image continuous_snd
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support hK
  · exact ((Real.continuous_fourierChar.comp ((continuous_snd.mul continuous_const).neg)).smul hF).continuousOn
  · intro x y _ hy
    have hzero : f (euclideanPairEquiv (x, y)) = 0 := by
      by_contra hh
      apply hy
      exact ⟨(x, y), subset_closure (show (x, y) ∈ support (f ∘ euclideanPairEquiv) from hh), rfl⟩
    rw [hzero, smul_zero]

theorem partialFourierPlane_integrable
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hc : Continuous f)
    (hf : HasCompactSupport f) (m : ℝ) : Integrable (partialFourierPlane f m) :=
  (partialFourierPlane_continuous hc hf m).integrable_of_hasCompactSupport
    (partialFourierPlane_hasCompactSupport hf m)

/-- Compact support supplies the decay hypothesis used by the available
one-dimensional Poisson theorem, without differentiating the partial integral. -/
theorem partialFourierPlane_isBigO
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : HasCompactSupport f) (m : ℝ) :
    partialFourierPlane f m =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 1
  have he := hasCompactSupport_iff_eventuallyEq.mp (partialFourierPlane_hasCompactSupport hf m)
  rw [Filter.coclosedCompact_eq_cocompact] at he
  filter_upwards [he] with x hx
  simp only [hx, Pi.zero_apply, norm_zero, one_mul]
  exact norm_nonneg _

/-- The one-dimensional Fourier transform of the partial transform is exactly
the actual two-dimensional Fourier transform. Fubini uses an integrable
modulation of the original compactly supported continuous function. -/
theorem partialFourierPlane_fourier
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hc : Continuous f)
    (hf : HasCompactSupport f) (m k : ℝ) :
    𝓕 (partialFourierPlane f m) k = 𝓕 f (euclideanPairEquiv (k, m)) := by
  let H : EuclideanSpace ℝ (Fin 2) → ℂ := fun z =>
    Real.fourierChar (-(inner ℝ z (euclideanPairEquiv (k, m)))) • f z
  have hHc : Continuous H :=
    (Real.continuous_fourierChar.comp ((continuous_id.inner continuous_const).neg)).smul hc
  have hHs : HasCompactSupport H := hf.smul_left
  have hHi : Integrable H := hHc.integrable_of_hasCompactSupport hHs
  have hphase (x y : ℝ) :
      Real.fourierChar (-(inner ℝ (euclideanPairEquiv (x, y)) (euclideanPairEquiv (k, m)))) =
        Real.fourierChar (-(x * k)) * Real.fourierChar (-(y * m)) := by
    rw [euclideanPairEquiv_inner]
    simp only [neg_add, AddChar.map_add_eq_mul]
  rw [Real.fourier_real_eq, Real.fourier_eq]
  change (∫ x : ℝ, Real.fourierChar (-(x * k)) • partialFourierPlane f m x) = ∫ z, H z
  rw [integral_euclidean_eq_integral_integral H hHi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [partialFourierPlane, Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only [H]
  rw [hphase, Circle.smul_def, Circle.coe_mul, smul_eq_mul]
  simp only [mul_assoc]

end Markov
