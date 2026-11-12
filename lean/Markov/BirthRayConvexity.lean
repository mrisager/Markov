import Markov.FrickeConvexity
import Markov.FrickeLengthTriangle

/-! Strict neighboring-ray inequalities at a Farey birth and in
all finite refinements, derived from the canonical trace lengths. -/

noncomputable section
attribute [-instance] DivisionRing.toRatAlgebra
local instance birthRayRatRealAlgebra : Algebra ℚ ℝ := DivisionRing.toRatAlgebra
open scoped QuadraticAlgebra

namespace Markov

/-- Advancing the trace recurrence multiplies its expanding coefficient by r. -/
theorem traceCoefficient_shift (t a b : ℤ) [ht : Fact (3 ≤ t)] :
    traceRoot t * traceCoefficient t a b = traceCoefficient t b (t * b - a) := by
  have hd := (traceDiscriminant_pos t ht.out).ne'
  ext <;> simp [traceCoefficient, traceRoot] <;> field_simp [hd] <;> ring

/-- At a Farey birth, the expanding coefficients on opposite sides are
related by conjugation and one extra root factor. -/
theorem traceCoefficient_birth_opposite (t a b : ℤ) [ht : Fact (3 ≤ t)] :
    traceCoefficient t b (t * b - a) =
      traceRoot t * star (traceCoefficient t a (t * a - b)) := by
  have hs : star (traceCoefficient t a (t * a - b)) = traceCoefficient t a b := by
    rw [traceCoefficient_star t a (t * a - b) ht.out]
    congr 1
    ring
  rw [hs, traceCoefficient_shift]

theorem traceWave_shift (r a a' : ℝ) (n : ℕ) :
    traceWave r (r * a) (r⁻¹ * a') n = traceWave r a a' (n + 1) := by
  simp only [traceWave, pow_succ]
  ring

/-- The opposite birth ray is the conjugate wave with index shifted by one. -/
theorem frickeRay_birth_opposite_wave (t a b : ℤ) [Fact (3 ≤ t)] (n : ℕ) :
    (frickeRay t b (t * b - a) n : ℝ) =
      traceWave (positiveTraceRoot t)
        (traceRealEmbedding t (star (traceCoefficient t a (t * a - b))))
        (traceRealEmbedding t (traceCoefficient t a (t * a - b))) (n + 1) := by
  rw [frickeRay_eq_traceWave, traceCoefficient_birth_opposite]
  simp only [star_mul, star_star, map_mul, traceRoot_star_eq_inv,
    map_inv₀, traceRealEmbedding_root]
  simpa only [mul_comm] using traceWave_shift (positiveTraceRoot t)
    (traceRealEmbedding t (star (traceCoefficient t a (t * a - b))))
    (traceRealEmbedding t (traceCoefficient t a (t * a - b))) n

/-- Strict convexity inequality for the two refined neighbor rays of a
birth direction. The extra 1 is the birth relation u+v=p. -/
theorem fricke_birth_length_corner (t a b : ℤ) [ht : Fact (3 ≤ t)]
    (ha : 0 < a) (hf : t ^ 2 + a ^ 2 + b ^ 2 = t * a * b) (m n : ℕ) :
    ((m + n + 1 : ℕ) : ℝ) * (2 * Real.log (positiveTraceRoot t)) <
      2 * Real.arcosh ((frickeRay t a (t * a - b) m : ℝ) / 2) +
        2 * Real.arcosh ((frickeRay t b (t * b - a) n : ℝ) / 2) := by
  have hf' : t ^ 2 + a ^ 2 + (t * a - b) ^ 2 = t * a * (t * a - b) := by
    nlinarith [hf]
  have hp := traceCoefficient_real_pos t a (t * a - b) ha hf'
  have hn : (1 : ℝ) < (Algebra.norm ℚ (traceCoefficient t a (t * a - b)) : ℝ) := by
    exact_mod_cast traceCoefficient_field_norm_gt_one t a (t * a - b) ht.out hf'
  rw [traceField_real_norm_eq] at hn
  have hh := traceWave_opposite_length_sum_gt (positiveTraceRoot t)
    (traceRealEmbedding t (traceCoefficient t a (t * a - b)))
    (traceRealEmbedding t (star (traceCoefficient t a (t * a - b))))
    (by linarith [positiveTraceRoot_gt_one t ht.out]) hp.1 hp.2 hn m (n + 1)
  rw [frickeRay_eq_traceWave t a (t * a - b) m, frickeRay_birth_opposite_wave]
  convert hh using 1
  push_cast
  ring

/-- The actual two neighboring rays in a refined Farey fan satisfy the
strict convexity inequality at their birth direction. All candidate lengths
refer to the canonical integer matrix assignment. -/
theorem FareyHolonomy.canonical_birth_corner
    {u v : ℤ × ℤ} {M N : IntMatrixTwo} (h : FareyHolonomy u v M N) (m n : ℕ)
    (hp : NonnegativePrimitiveDirection (u + v))
    (hq : NonnegativePrimitiveDirection (m • (u + v) + u))
    (hr : NonnegativePrimitiveDirection (n • (u + v) + v)) :
    ((m + n + 1 : ℕ) : ℝ) * primitiveFareyLength (u + v) hp <
      primitiveFareyLength (m • (u + v) + u) hq +
        primitiveFareyLength (n • (u + v) + v) hr := by
  have H := h.positiveFrickePair
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
  have hleft : FareyHolonomy (m • (u + v) + u) (u + v) (M * (M * N) ^ m) (M * N) := by
    simpa only [add_comm] using h.left.right_integral_ray m
  have hright := h.right.integral_ray n
  have hqT : primitiveFareyTrace (m • (u + v) + u) hq =
      frickeRay (M * N).trace M.trace ((M * N).trace * M.trace - N.trace) m := by
    rw [primitiveFareyTrace, hleft.primitiveFareyMatrix_left hq,
      Matrix.trace_mul_comm M ((M * N) ^ m),
      matrix_trace_ray_eq_frickeRay (M * N) M hdetMN, hc1]
  have hrT : primitiveFareyTrace (n • (u + v) + v) hr =
      frickeRay (M * N).trace N.trace ((M * N).trace * N.trace - M.trace) n := by
    rw [primitiveFareyTrace, hright.primitiveFareyMatrix_right hr,
      matrix_trace_ray_eq_frickeRay (M * N) N hdetMN, hc2]
  have hpT : primitiveFareyTrace (u + v) hp = (M * N).trace := by
    rw [primitiveFareyTrace, h.right.primitiveFareyMatrix_left hp]
  have hpL : primitiveFareyLength (u + v) hp = 2 * Real.log (positiveTraceRoot (M * N).trace) := by
    apply traceLength_eq_two_log_root (M * N).trace H.trace_product _
      (primitiveFareyLength_pos _ hp).le
    rw [← hpT]
    exact primitiveFareyTrace_eq_two_cosh _ hp
  have hb := fricke_birth_length_corner (M * N).trace M.trace N.trace
    (by linarith [H.trace_left]) hf m n
  rw [hpL]
  simpa only [primitiveFareyLength, hqT, hrT] using hb

end Markov
