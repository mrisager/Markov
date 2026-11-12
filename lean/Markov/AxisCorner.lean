import Markov.FareyHolonomy
import Markov.FrickeConvexity

/-! Opposite-ray length inequalities at seed axes. The second ray uses the
inverse matrix of the neighboring seed, represented by its adjugate. These
are actual matrix trace identities and Fricke estimates; no norm is assumed. -/

namespace Markov

/-- The adjugate has the same trace in dimension two. -/
theorem matrix_two_trace_adjugate {R : Type*} [CommRing R]
    (N : Matrix (Fin 2) (Fin 2) R) : N.adjugate.trace = N.trace := by
  simp [Matrix.adjugate_fin_two, Matrix.trace, Matrix.diag_apply]
  ring

/-- The opposite trace is obtained from the actual two-by-two adjugate. -/
theorem matrix_two_trace_mul_adjugate {R : Type*} [CommRing R]
    (M N : Matrix (Fin 2) (Fin 2) R) :
    (M * N.adjugate).trace = M.trace * N.trace - (M * N).trace := by
  simp [Matrix.adjugate_fin_two, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Both matrix rays realize the two opposite integer Fricke recurrences. -/
theorem positiveFrickePair_opposite_matrix_rays (M N : IntMatrixTwo)
    (hp : PositiveFrickePair M N) (n m : ℕ) :
    (M ^ n * N).trace = frickeRay M.trace N.trace (M * N).trace n ∧
      (M ^ m * N.adjugate).trace =
        frickeRay M.trace N.trace (M.trace * N.trace - (M * N).trace) m := by
  refine ⟨matrix_trace_ray_eq_frickeRay M N hp.det_left n, ?_⟩
  simpa only [matrix_two_trace_adjugate, matrix_two_trace_mul_adjugate]
    using matrix_trace_ray_eq_frickeRay M N.adjugate hp.det_left m

/-- The strict corner inequality at a seed axis, valid for arbitrary ray
indices on its two sides. The expanding root and traces are the actual ones
of the positive Fricke matrix pair. -/
theorem positiveFrickePair_axis_corner (M N : IntMatrixTwo)
    (hp : PositiveFrickePair M N) (n m : ℕ) :
    2 * (((n : ℝ) + (m : ℝ)) * Real.log (positiveTraceRoot M.trace)) <
      2 * Real.arcosh (((M ^ n * N).trace : ℝ) / 2) +
        2 * Real.arcosh (((M ^ m * N.adjugate).trace : ℝ) / 2) := by
  letI : Fact (3 ≤ M.trace) := ⟨hp.trace_left⟩
  have hh := frickeRay_opposite_length_sum_gt M.trace N.trace (M * N).trace
    (by linarith [hp.trace_right]) hp.fricke n m
  rcases positiveFrickePair_opposite_matrix_rays M N hp n m with ⟨hn, hm⟩
  simpa only [← hn, ← hm] using hh

/-- Equal refinement depths give the axis-ray inequality for the two
neighbors whose direction sum is `2n` times the axis direction. -/
theorem positiveFrickePair_axis_corner_equal (M N : IntMatrixTwo)
    (hp : PositiveFrickePair M N) (n : ℕ) :
    4 * (n : ℝ) * Real.log (positiveTraceRoot M.trace) <
      2 * Real.arcosh (((M ^ n * N).trace : ℝ) / 2) +
        2 * Real.arcosh (((M ^ n * N.adjugate).trace : ℝ) / 2) := by
  convert positiveFrickePair_axis_corner M N hp n n using 1
  ring

end Markov
