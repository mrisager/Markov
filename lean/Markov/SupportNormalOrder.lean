import Markov.NormalDeterminant

/-! Order of actual supporting normals along an affine section of a normed
plane. The determinant sign is proved from the norming inequalities, with
no assumed ordering of angular coordinates. At one parameter a norm may
have several supports; their order is exactly their second evaluation.
This module does not provide a cutoff angular-tail estimate. -/

noncomputable section

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Subgradients of the restriction of a norm to an affine line are
monotone, for arbitrary independent choices of norming functionals. -/
theorem normingSupport_parameter_subgradient_mono (a b : E) (s t : ℝ)
    (hst : s < t) (fs ft : StrongDual ℝ E)
    (hfs : fs ∈ normingFunctionals (a + s • b))
    (hft : ft ∈ normingFunctionals (a + t • b)) : fs b ≤ ft b := by
  have hs := normingFunctional_le_norm (a + s • b) (a + t • b) fs hfs
  have ht := normingFunctional_le_norm (a + t • b) (a + s • b) ft hft
  have hes := hfs.2
  have het := hft.2
  simp only [map_add, map_smul, smul_eq_mul] at hs ht hes het
  have hmul : (t - s) * (fs b - ft b) ≤ 0 := by nlinarith only [hs, ht, hes, het]
  exact le_of_not_gt (fun h => (not_lt_of_ge hmul)
    (mul_pos (sub_pos.mpr hst) (sub_pos.mpr h)))

/-- The signed determinant of actual supports is nonnegative as the
parameter increases. Symmetry of the norm supplies both lower support
bounds needed when the second evaluations have opposite signs. -/
theorem normingSupport_affineLine_det_nonneg (a b : E) (s t : ℝ)
    (hst : s < t) (fs ft : StrongDual ℝ E)
    (hfs : fs ∈ normingFunctionals (a + s • b))
    (hft : ft ∈ normingFunctionals (a + t • b)) :
    0 ≤ fs a * ft b - fs b * ft a := by
  let F := ‖a + s • b‖
  let G := ‖a + t • b‖
  let q := fs b
  let r := ft b
  let d := t - s
  have hF : 0 ≤ F := norm_nonneg _
  have hG : 0 ≤ G := norm_nonneg _
  have hqr : q ≤ r := normingSupport_parameter_subgradient_mono a b s t hst fs ft hfs hft
  have hes : fs a + s * q = F := by simpa [F, q] using hfs.2
  have het : ft a + t * r = G := by simpa [G, r] using hft.2
  have hsu : F + d * q ≤ G := by
    have h := normingFunctional_le_norm (a + s • b) (a + t • b) fs hfs
    simp only [map_add, map_smul, smul_eq_mul] at h
    change fs a + t * q ≤ G at h
    dsimp only [d]
    nlinarith only [hes, h]
  have htu : G - d * r ≤ F := by
    have h := normingFunctional_le_norm (a + t • b) (a + s • b) ft hft
    simp only [map_add, map_smul, smul_eq_mul] at h
    change ft a + s * r ≤ F at h
    dsimp only [d]
    nlinarith only [het, h]
  have hsl : -G ≤ F + d * q := by
    have h := normingFunctional_le_norm (a + s • b) (-(a + t • b)) fs hfs
    simp only [map_neg, map_add, map_smul, smul_eq_mul, norm_neg] at h
    change -(fs a + t * q) ≤ G at h
    dsimp only [d]
    nlinarith only [hes, h]
  have htl : -F ≤ G - d * r := by
    have h := normingFunctional_le_norm (a + t • b) (-(a + s • b)) ft hft
    simp only [map_neg, map_add, map_smul, smul_eq_mul, norm_neg] at h
    change -(ft a + s * r) ≤ F at h
    dsimp only [d]
    nlinarith only [het, h]
  have hid : fs a * ft b - fs b * ft a = F * r - G * q + d * q * r := by
    calc
      _ = (fs a + s * q) * r - (ft a + t * r) * q + d * q * r := by
        dsimp [q, r, d]
        ring
      _ = _ := by rw [hes, het]
  rw [hid]
  by_cases hq : 0 ≤ q
  · have hm := mul_le_mul_of_nonneg_right htu hq
    have hp := mul_nonneg hF (sub_nonneg.mpr hqr)
    nlinarith only [hm, hp]
  · by_cases hr : r ≤ 0
    · have hm := mul_le_mul_of_nonpos_right hsu hr
      have hp := mul_nonneg hG (sub_nonneg.mpr hqr)
      nlinarith only [hm, hp]
    · have hqn : 0 ≤ -q := by linarith
      have hrp : 0 ≤ r := by linarith
      by_cases hsum : 0 ≤ q + r
      · have hm := mul_nonneg hqn (show 0 ≤ F + G - d * r by linarith only [htl])
        have hp := mul_nonneg hF hsum
        nlinarith only [hm, hp]
      · have hm := mul_nonneg hrp (show 0 ≤ F + G + d * q by linarith only [hsl])
        have hp := mul_nonneg hG (show 0 ≤ -(q + r) by linarith)
        nlinarith only [hm, hp]

/-- In actual Euclidean dual coordinates the determinant has the same
orientation as the affine parameter. -/
theorem normingSupport_basisLine_euclideanDet_nonneg
    (B : Module.Basis (Fin 2) ℝ E) (s t : ℝ) (hst : s < t)
    (fs ft : StrongDual ℝ E)
    (hfs : fs ∈ normingFunctionals (B 0 + s • B 1))
    (hft : ft ∈ normingFunctionals (B 0 + t • B 1)) :
    0 ≤ euclideanPlaneDet (euclideanDualCoordinates B fs)
      (euclideanDualCoordinates B ft) :=
  normingSupport_affineLine_det_nonneg (B 0) (B 1) s t hst fs ft hfs hft

/-- Positive radial normalization preserves the determinant orientation
of the actual Euclidean unit normal directions. -/
theorem normingSupport_basisLine_normalizedDet_nonneg
    (B : Module.Basis (Fin 2) ℝ E) (s t : ℝ) (hst : s < t)
    (fs ft : StrongDual ℝ E)
    (hfs : fs ∈ normingFunctionals (B 0 + s • B 1))
    (hft : ft ∈ normingFunctionals (B 0 + t • B 1)) :
    0 ≤ euclideanPlaneDet (normalizedEuclideanCovector B fs)
      (normalizedEuclideanCovector B ft) := by
  unfold normalizedEuclideanCovector NormedSpace.normalize
  rw [euclideanPlaneDet_smul_left, euclideanPlaneDet_smul_right]
  exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
    (mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
      (normingSupport_basisLine_euclideanDet_nonneg B s t hst fs ft hfs hft))

/-- At one parameter, the support fibre can have nonzero length. Its
signed determinant is the norm of the point times the second-evaluation
difference. -/
theorem normingSupport_sameParameter_det_eq (a b : E) (t : ℝ)
    (f g : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals (a + t • b))
    (hg : g ∈ normingFunctionals (a + t • b)) :
    f a * g b - f b * g a = ‖a + t • b‖ * (g b - f b) := by
  have hfe := hf.2
  have hge := hg.2
  simp only [map_add, map_smul, smul_eq_mul] at hfe hge
  calc
    _ = (f a + t * f b) * g b - f b * (g a + t * g b) := by ring
    _ = _ := by rw [hfe, hge]; ring

/-- A basis section never passes through zero, so the order on a support
fibre is exactly its second-evaluation order. -/
theorem normingSupport_basisLine_sameParameter_det_nonneg_iff
    (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) (f g : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals (B 0 + t • B 1))
    (hg : g ∈ normingFunctionals (B 0 + t • B 1)) :
    0 ≤ f (B 0) * g (B 1) - f (B 1) * g (B 0) ↔ f (B 1) ≤ g (B 1) := by
  rw [normingSupport_sameParameter_det_eq (B 0) (B 1) t f g hf hg]
  exact (mul_nonneg_iff_of_pos_left
    (norm_pos_iff.mpr (basis_affineLine_ne_zero B t))).trans sub_nonneg

/-- The support selected by the increasing parameter direction is the
last support of its own fibre in the determinant order. -/
theorem isSelectedSupport_affineLine_det_nonneg (a b : E) (t : ℝ)
    (f g : StrongDual ℝ E) (hf : IsSelectedSupport (a + t • b) b f)
    (hg : g ∈ normingFunctionals (a + t • b)) :
    0 ≤ g a * f b - g b * f a := by
  rw [normingSupport_sameParameter_det_eq a b t g f hg hf.1]
  exact mul_nonneg (norm_nonneg _) (sub_nonneg.mpr (hf.2 g hg))

end Markov
