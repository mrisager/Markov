import Markov.AngularNormals

/-! Elementary comparisons between angular width, Euclidean chord length,
and distances between normalized covectors. -/

noncomputable section

namespace Markov

/-- The exact Euclidean chord formula for the real circle parameterization. -/
theorem dist_circleNormal_eq_two_abs_sin_half (a b : ℝ) :
    dist (circleNormal a) (circleNormal b) = 2 * |Real.sin ((a - b) / 2)| := by
  have hnorm : ‖circleNormal a - circleNormal b‖ ^ 2 =
      (Real.cos a - Real.cos b) ^ 2 + (Real.sin a - Real.sin b) ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, circleNormal]
  have hcos : Real.cos (a - b) =
      Real.cos a * Real.cos b + Real.sin a * Real.sin b := Real.cos_sub a b
  have hdouble : Real.cos (a - b) = 1 - 2 * Real.sin ((a - b) / 2) ^ 2 := by
    have hc := Real.cos_two_mul ((a - b) / 2)
    have hs := Real.sin_sq_add_cos_sq ((a - b) / 2)
    have heq : 2 * ((a - b) / 2) = a - b := by ring
    rw [heq] at hc
    nlinarith
  have ha := Real.sin_sq_add_cos_sq a
  have hb := Real.sin_sq_add_cos_sq b
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (circleNormal a - circleNormal b),
    abs_nonneg (Real.sin ((a - b) / 2)), sq_abs (Real.sin ((a - b) / 2))]

/-- On an arc of angular width at most `π`, the angle is bounded by
`π / 2` times the Euclidean chord distance. -/
theorem abs_sub_le_pi_div_two_mul_dist_circleNormal (a b : ℝ)
    (hab : |a - b| ≤ Real.pi) :
    |a - b| ≤ (Real.pi / 2) * dist (circleNormal a) (circleNormal b) := by
  have hhalf : |(a - b) / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hs : |a - b| / Real.pi ≤ |Real.sin ((a - b) / 2)| := by
    have h := Real.mul_abs_le_abs_sin hhalf
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    convert h using 1
    ring
  have hm := (div_le_iff₀ Real.pi_pos).mp hs
  rw [dist_circleNormal_eq_two_abs_sin_half]
  nlinarith

/-- Ordered-endpoint form of the inverse chord estimate for a short arc. -/
theorem sub_le_pi_div_two_mul_dist_circleNormal (a b : ℝ)
    (hab : a ≤ b) (hshort : b - a ≤ Real.pi) :
    b - a ≤ (Real.pi / 2) * dist (circleNormal a) (circleNormal b) := by
  have habs : |a - b| = b - a := by
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  have h := abs_sub_le_pi_div_two_mul_dist_circleNormal a b (by rwa [habs])
  rwa [habs] at h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalization is `2 / r`-Lipschitz between vectors whose norms are at
least the positive radius `r`. -/
theorem normalize_dist_le_of_norm_lower_bound (x y : E) (r : ℝ) (hr : 0 < r)
    (hx : r ≤ ‖x‖) (hy : r ≤ ‖y‖) :
    dist (NormedSpace.normalize x) (NormedSpace.normalize y) ≤ (2 / r) * dist x y := by
  simpa only [dist_eq_norm] using normalize_sub_le_of_norm_lower_bound x y r hr hx hy

/-- The same positive-radius comparison for actual Euclidean covector
coordinates and their normalized normal directions. -/
theorem normalizedEuclideanCovector_dist_le_of_norm_lower_bound
    (B : Module.Basis (Fin 2) ℝ E) (f g : StrongDual ℝ E) (r : ℝ) (hr : 0 < r)
    (hf : r ≤ ‖euclideanDualCoordinates B f‖)
    (hg : r ≤ ‖euclideanDualCoordinates B g‖) :
    dist (normalizedEuclideanCovector B f) (normalizedEuclideanCovector B g) ≤
      (2 / r) * dist (euclideanDualCoordinates B f) (euclideanDualCoordinates B g) :=
  normalize_dist_le_of_norm_lower_bound _ _ r hr hf hg

end Markov
