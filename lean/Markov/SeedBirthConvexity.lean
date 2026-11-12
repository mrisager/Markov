import Markov.BirthRayConvexity
import Markov.SeedCanonical

/-! Canonical birth-corner convexity for an arbitrary positive Fricke seed.
The matrix words and their primitive lengths are constructed explicitly;
no norm compatibility or interpolation property is assumed. -/

noncomputable section

namespace Markov

/-- Every finite refinement of a birth corner obeys the strict length
inequality for any positive Fricke seed, including the mixed-sign seed. -/
theorem SeededFarey.canonical_seed_birth_corner
    {M0 N0 : IntMatrixTwo} {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N)
    (h0 : PositiveFrickePair M0 N0) (m n : ℕ)
    (hp : NonnegativePrimitiveDirection (u + v))
    (hq : NonnegativePrimitiveDirection (m • (u + v) + u))
    (hr : NonnegativePrimitiveDirection (n • (u + v) + v)) :
    ((m + n + 1 : ℕ) : ℝ) * primitiveSeedLength M0 N0 (u + v) hp <
      primitiveSeedLength M0 N0 (m • (u + v) + u) hq +
        primitiveSeedLength M0 N0 (n • (u + v) + v) hr := by
  have H := h.positiveFrickePair h0
  have hdetMN : (M * N).det = 1 := by rw [Matrix.det_mul, H.det_left, H.det_right]; norm_num
  letI : Fact (3 ≤ (M * N).trace) := ⟨H.trace_product⟩
  have hf : (M * N).trace ^ 2 + M.trace ^ 2 + N.trace ^ 2 =
      (M * N).trace * M.trace * N.trace := by nlinarith [H.fricke]
  have hc1 : ((M * N) * M).trace = (M * N).trace * M.trace - N.trace := by
    rw [Matrix.trace_mul_comm (M * N) M, matrix_trace_left_move M N H.det_left]
    ring
  have hc2 : ((M * N) * N).trace = (M * N).trace * N.trace - M.trace := by
    rw [matrix_trace_right_move M N H.det_right]
    ring
  have hleft : SeededFarey (1, 0) (0, 1) M0 N0
      (m • (u + v) + u) (u + v) (M * (M * N) ^ m) (M * N) := by
    simpa only [add_comm] using h.left.right_integral_ray m
  have hright := h.right.integral_ray n
  have hqT : primitiveSeedTrace M0 N0 (m • (u + v) + u) hq =
      frickeRay (M * N).trace M.trace ((M * N).trace * M.trace - N.trace) m := by
    rw [primitiveSeedTrace, hleft.primitiveSeedMatrix_left hq,
      Matrix.trace_mul_comm M ((M * N) ^ m),
      matrix_trace_ray_eq_frickeRay (M * N) M hdetMN, hc1]
  have hrT : primitiveSeedTrace M0 N0 (n • (u + v) + v) hr =
      frickeRay (M * N).trace N.trace ((M * N).trace * N.trace - M.trace) n := by
    rw [primitiveSeedTrace, hright.primitiveSeedMatrix_right hr,
      matrix_trace_ray_eq_frickeRay (M * N) N hdetMN, hc2]
  have hpT : primitiveSeedTrace M0 N0 (u + v) hp = (M * N).trace := by
    rw [primitiveSeedTrace, h.right.primitiveSeedMatrix_left hp]
  have hpL : primitiveSeedLength M0 N0 (u + v) hp =
      2 * Real.log (positiveTraceRoot (M * N).trace) := by
    apply traceLength_eq_two_log_root (M * N).trace H.trace_product _
      (primitiveSeedLength_pos M0 N0 h0 _ hp).le
    rw [← hpT]
    exact primitiveSeedTrace_eq_two_cosh M0 N0 h0 _ hp
  have hb := fricke_birth_length_corner (M * N).trace M.trace N.trace
    (by linarith [H.trace_left]) hf m n
  rw [hpL]
  simpa only [primitiveSeedLength, hqT, hrT] using hb

end Markov
