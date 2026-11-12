import Markov.HalfPlaneAngleOrder
import Markov.ChordHalfPlane
import Markov.ShortNormalArc

/-! The positive-sum half-plane gives a single short branch for actual support
angles. Hence Euclidean distances between the normalized support covectors
control their real angular differences on a whole equal-length chord. -/

noncomputable section

namespace Markov

/-- The explicit arctangent branch stays in an open interval of width `π`. -/
theorem complex_arg_mem_Ioo_of_sum_pos (z : ℂ) (hz : 0 < z.re + z.im) :
    z.arg ∈ Set.Ioo (-(Real.pi / 4)) (3 * Real.pi / 4) := by
  rw [complex_arg_eq_arctan_of_sum_pos z hz]
  have hlo := Real.neg_pi_div_two_lt_arctan ((z.im - z.re) / (z.re + z.im))
  have hhi := Real.arctan_lt_pi_div_two ((z.im - z.re) / (z.re + z.im))
  constructor <;> linarith

/-- Arguments in this common open half-plane differ by strictly less than `π`. -/
theorem abs_complex_arg_sub_lt_pi_of_sum_pos (z w : ℂ)
    (hz : 0 < z.re + z.im) (hw : 0 < w.re + w.im) :
    |z.arg - w.arg| < Real.pi := by
  rcases complex_arg_mem_Ioo_of_sum_pos z hz with ⟨hzlo, hzhi⟩
  rcases complex_arg_mem_Ioo_of_sum_pos w hw with ⟨hwlo, hwhi⟩
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem supportAngle_mem_Ioo_of_sum_pos
    (B : Module.Basis (Fin 2) ℝ E) (f : StrongDual ℝ E)
    (hf : 0 < f (B 0) + f (B 1)) :
    supportAngle B f ∈ Set.Ioo (-(Real.pi / 4)) (3 * Real.pi / 4) :=
  complex_arg_mem_Ioo_of_sum_pos (supportComplex B f) hf

theorem abs_supportAngle_sub_lt_pi_of_sum_pos
    (B : Module.Basis (Fin 2) ℝ E) (f g : StrongDual ℝ E)
    (hf : 0 < f (B 0) + f (B 1)) (hg : 0 < g (B 0) + g (B 1)) :
    |supportAngle B f - supportAngle B g| < Real.pi :=
  abs_complex_arg_sub_lt_pi_of_sum_pos (supportComplex B f) (supportComplex B g) hf hg

theorem supportAngle_sub_lt_pi_of_sum_pos
    (B : Module.Basis (Fin 2) ℝ E) (f g : StrongDual ℝ E)
    (hf : 0 < f (B 0) + f (B 1)) (hg : 0 < g (B 0) + g (B 1)) :
    supportAngle B g - supportAngle B f < Real.pi :=
  (le_abs_self _).trans_lt (abs_supportAngle_sub_lt_pi_of_sum_pos B g f hg hf)

/-- The inverse short-chord estimate now applies to these actual support
angles; the common half-plane proves its branch hypothesis. -/
theorem abs_supportAngle_sub_le_pi_div_two_mul_dist_of_sum_pos
    (B : Module.Basis (Fin 2) ℝ E) (f g : StrongDual ℝ E)
    (hf : 0 < f (B 0) + f (B 1)) (hg : 0 < g (B 0) + g (B 1)) :
    |supportAngle B f - supportAngle B g| ≤
      (Real.pi / 2) *
        dist (normalizedEuclideanCovector B f) (normalizedEuclideanCovector B g) := by
  have hfne : f ≠ 0 := by
    intro h
    simp [h] at hf
  have hgne : g ≠ 0 := by
    intro h
    simp [h] at hg
  have h := abs_sub_le_pi_div_two_mul_dist_circleNormal
    (supportAngle B f) (supportAngle B g)
    (abs_supportAngle_sub_lt_pi_of_sum_pos B f g hf hg).le
  rwa [circleNormal_supportAngle B f hfne, circleNormal_supportAngle B g hgne] at h

theorem supportAngle_sub_le_pi_div_two_mul_dist_of_sum_pos
    (B : Module.Basis (Fin 2) ℝ E) (f g : StrongDual ℝ E)
    (hf : 0 < f (B 0) + f (B 1)) (hg : 0 < g (B 0) + g (B 1)) :
    supportAngle B g - supportAngle B f ≤
      (Real.pi / 2) *
        dist (normalizedEuclideanCovector B f) (normalizedEuclideanCovector B g) := by
  calc
    supportAngle B g - supportAngle B f ≤ |supportAngle B f - supportAngle B g| :=
      by linarith [neg_le_abs (supportAngle B f - supportAngle B g)]
    _ ≤ _ := abs_supportAngle_sub_le_pi_div_two_mul_dist_of_sum_pos B f g hf hg

/-- All supports anywhere over the closed chord share this short real branch. -/
theorem normingSupport_chord_abs_supportAngle_sub_lt_pi
    (B : Module.Basis (Fin 2) ℝ E) (L s t : ℝ)
    (h0 : ‖B 0‖ = L) (h1 : ‖B 1‖ = L) (hdiff : ‖B 0 - B 1‖ < 2 * L)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (f g : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals ((1 - s) • B 0 + s • B 1))
    (hg : g ∈ normingFunctionals ((1 - t) • B 0 + t • B 1)) :
    |supportAngle B f - supportAngle B g| < Real.pi := by
  apply abs_supportAngle_sub_lt_pi_of_sum_pos B f g
  · simpa only [map_add] using normingFunctional_sum_pos_on_equal_norm_chord
      (B 0) (B 1) L s h0 h1 hdiff hs f hf
  · simpa only [map_add] using normingFunctional_sum_pos_on_equal_norm_chord
      (B 0) (B 1) L t h0 h1 hdiff ht g hg

theorem normingSupport_chord_supportAngle_sub_lt_pi
    (B : Module.Basis (Fin 2) ℝ E) (L s t : ℝ)
    (h0 : ‖B 0‖ = L) (h1 : ‖B 1‖ = L) (hdiff : ‖B 0 - B 1‖ < 2 * L)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (f g : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals ((1 - s) • B 0 + s • B 1))
    (hg : g ∈ normingFunctionals ((1 - t) • B 0 + t • B 1)) :
    supportAngle B g - supportAngle B f < Real.pi :=
  (le_abs_self _).trans_lt
    (normingSupport_chord_abs_supportAngle_sub_lt_pi B L t s h0 h1 hdiff ht hs g f hg hf)

/-- On the whole equal-length chord the actual angle difference is bounded
by the distance between the normalized actual covectors. -/
theorem normingSupport_chord_abs_supportAngle_sub_le_pi_div_two_mul_dist
    (B : Module.Basis (Fin 2) ℝ E) (L s t : ℝ)
    (h0 : ‖B 0‖ = L) (h1 : ‖B 1‖ = L) (hdiff : ‖B 0 - B 1‖ < 2 * L)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (f g : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals ((1 - s) • B 0 + s • B 1))
    (hg : g ∈ normingFunctionals ((1 - t) • B 0 + t • B 1)) :
    |supportAngle B f - supportAngle B g| ≤
      (Real.pi / 2) *
        dist (normalizedEuclideanCovector B f) (normalizedEuclideanCovector B g) := by
  apply abs_supportAngle_sub_le_pi_div_two_mul_dist_of_sum_pos B f g
  · simpa only [map_add] using normingFunctional_sum_pos_on_equal_norm_chord
      (B 0) (B 1) L s h0 h1 hdiff hs f hf
  · simpa only [map_add] using normingFunctional_sum_pos_on_equal_norm_chord
      (B 0) (B 1) L t h0 h1 hdiff ht g hg

theorem normingSupport_chord_supportAngle_sub_le_pi_div_two_mul_dist
    (B : Module.Basis (Fin 2) ℝ E) (L s t : ℝ)
    (h0 : ‖B 0‖ = L) (h1 : ‖B 1‖ = L) (hdiff : ‖B 0 - B 1‖ < 2 * L)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (f g : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals ((1 - s) • B 0 + s • B 1))
    (hg : g ∈ normingFunctionals ((1 - t) • B 0 + t • B 1)) :
    supportAngle B g - supportAngle B f ≤
      (Real.pi / 2) *
        dist (normalizedEuclideanCovector B f) (normalizedEuclideanCovector B g) := by
  calc
    supportAngle B g - supportAngle B f ≤ |supportAngle B f - supportAngle B g| :=
      by linarith [neg_le_abs (supportAngle B f - supportAngle B g)]
    _ ≤ _ := normingSupport_chord_abs_supportAngle_sub_le_pi_div_two_mul_dist
      B L s t h0 h1 hdiff hs ht f g hf hg

end Markov
