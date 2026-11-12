import Markov.NormalDeterminant

/-! Small differences on a unimodular integral pair control the full
Euclidean difference of two support covectors. This coordinate estimate
does not assume a bound on an entire normal arc. -/

noncomputable section

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Reconstruct a covector difference from its values on an integral
unimodular pair, with explicit height loss. -/
theorem euclideanDualCoordinates_dist_le_pair_values
    (B : Module.Basis (Fin 2) ℝ E) (f g : StrongDual ℝ E)
    (u v : ℤ × ℤ) (hdet : |intDet u v| = 1)
    (δu δv : ℝ) (hu : |f (intVector B u) - g (intVector B u)| ≤ δu)
    (hv : |f (intVector B v) - g (intVector B v)| ≤ δv) :
    dist (euclideanDualCoordinates B f) (euclideanDualCoordinates B g) ≤
      2 * (δu * intHeight v + δv * intHeight u) := by
  have hd : |(intDet u v : ℝ)| = 1 := by exact_mod_cast hdet
  have hδu : 0 ≤ δu := (abs_nonneg _).trans hu
  have hδv : 0 ≤ δv := (abs_nonneg _).trans hv
  have h0 : (f (B 0) - g (B 0)) * (intDet u v : ℝ) =
      (f (intVector B u) - g (intVector B u)) * (v.2 : ℝ) -
        (f (intVector B v) - g (intVector B v)) * (u.2 : ℝ) := by
    simp [intVector, intDet]
    ring
  have h1 : (f (B 1) - g (B 1)) * (intDet u v : ℝ) =
      (f (intVector B v) - g (intVector B v)) * (u.1 : ℝ) -
        (f (intVector B u) - g (intVector B u)) * (v.1 : ℝ) := by
    simp [intVector, intDet]
    ring
  have hb0 : |f (B 0) - g (B 0)| ≤ δu * intHeight v + δv * intHeight u := by
    have hh := congrArg abs h0
    rw [abs_mul, hd, mul_one] at hh
    rw [hh]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_mul]
    exact add_le_add
      (mul_le_mul hu (le_max_right _ _) (abs_nonneg _) hδu)
      (mul_le_mul hv (le_max_right _ _) (abs_nonneg _) hδv)
  have hb1 : |f (B 1) - g (B 1)| ≤ δu * intHeight v + δv * intHeight u := by
    have hh := congrArg abs h1
    rw [abs_mul, hd, mul_one] at hh
    rw [hh]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_mul]
    simpa only [add_comm] using add_le_add
      (mul_le_mul hv (le_max_left _ _) (abs_nonneg _) hδv)
      (mul_le_mul hu (le_max_left _ _) (abs_nonneg _) hδu)
  have hC : 0 ≤ δu * intHeight v + δv * intHeight u :=
    add_nonneg (mul_nonneg hδu (intHeight_nonneg v))
      (mul_nonneg hδv (intHeight_nonneg u))
  have hs : dist (euclideanDualCoordinates B f) (euclideanDualCoordinates B g) ^ 2 =
      (f (B 0) - g (B 0)) ^ 2 + (f (B 1) - g (B 1)) ^ 2 := by
    rw [dist_eq_norm]
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs]
  have hb0s := (sq_le_sq₀ (abs_nonneg _) hC).mpr hb0
  have hb1s := (sq_le_sq₀ (abs_nonneg _) hC).mpr hb1
  rw [sq_abs] at hb0s hb1s
  nlinarith [dist_nonneg (x := euclideanDualCoordinates B f)
    (y := euclideanDualCoordinates B g)]

/-- A common evaluation-error bound costs only the sum of endpoint heights. -/
theorem euclideanDualCoordinates_dist_le_uniform_pair_values
    (B : Module.Basis (Fin 2) ℝ E) (f g : StrongDual ℝ E)
    (u v : ℤ × ℤ) (hdet : |intDet u v| = 1) (δ : ℝ)
    (hu : |f (intVector B u) - g (intVector B u)| ≤ δ)
    (hv : |f (intVector B v) - g (intVector B v)| ≤ δ) :
    dist (euclideanDualCoordinates B f) (euclideanDualCoordinates B g) ≤
      2 * (intHeight u + intHeight v) * δ := by
  simpa only [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc, add_comm] using
    euclideanDualCoordinates_dist_le_pair_values B f g u v hdet δ δ hu hv

end Markov
