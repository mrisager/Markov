import Markov.TraceSectionSampling

/-! One scale threshold makes the section-sampling mesh small enough
uniformly over all nonzero integer directions and all unit normal directions. -/

noncomputable section

namespace Markov

/-- A nonzero standard integer direction has Euclidean norm at least one. -/
theorem one_le_norm_euclideanIntDirection {k : ℤ × ℤ} (hk : k ≠ (0, 0)) :
    1 ≤ ‖euclideanIntDirection k‖ := by
  rw [euclideanIntDirection_norm]
  exact intEuclidean_ge_one k hk

/-- The explicit uniform radial threshold is positive. -/
theorem trace_radial_scale_pos_of_threshold {S : ℝ}
    (hS : 8 / traceEuclideanInradius + 1 ≤ S) : 0 < S := by
  have hp : 0 < 8 / traceEuclideanInradius := div_pos (by norm_num) traceEuclideanInradius_pos
  linarith

/-- The reciprocal radial frequency mesh is positive and smaller than
one eighth of every actual unit-normal projection interval. -/
theorem trace_radial_sampling_step_bounds
    {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1)
    {k : ℤ × ℤ} (hk : k ≠ (0, 0)) {S : ℝ}
    (hS : 8 / traceEuclideanInradius + 1 ≤ S) :
    0 < (S * ‖euclideanIntDirection k‖)⁻¹ ∧
      (S * ‖euclideanIntDirection k‖)⁻¹ <
        (traceEuclideanSupportHeight θ + traceEuclideanSupportHeight (-θ)) / 8 := by
  have hSpos := trace_radial_scale_pos_of_threshold hS
  have hk1 := one_le_norm_euclideanIntDirection hk
  have hkpos : 0 < ‖euclideanIntDirection k‖ := by linarith
  have hprod : 0 < S * ‖euclideanIntDirection k‖ := mul_pos hSpos hkpos
  refine ⟨inv_pos.mpr hprod, ?_⟩
  have hSr : 8 < S * traceEuclideanInradius := by
    have hm := mul_le_mul_of_nonneg_right hS traceEuclideanInradius_pos.le
    rw [add_mul, div_mul_cancel₀ _ traceEuclideanInradius_pos.ne', one_mul] at hm
    linarith [traceEuclideanInradius_pos]
  have hG : 8 < traceEuclideanInradius * (S * ‖euclideanIntDirection k‖) := by
    have hm := mul_le_mul_of_nonneg_left hk1
      (mul_nonneg hSpos.le traceEuclideanInradius_pos.le)
    nlinarith
  have hstep : (S * ‖euclideanIntDirection k‖)⁻¹ < traceEuclideanInradius / 8 := by
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ hprod).2
    nlinarith
  have hp := traceEuclideanInradius_le_supportHeight hθ
  have hm := traceEuclideanInradius_le_supportHeight (show ‖-θ‖ = 1 by simpa using hθ)
  exact hstep.trans_le (by linarith [traceEuclideanInradius_pos])

end Markov
