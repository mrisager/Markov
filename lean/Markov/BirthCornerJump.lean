import Markov.BirthRayConvexity
import Markov.CornerJumpBounds
import Markov.NormedPlane

/-! The actual coefficient identity behind a Farey birth corner.
The root factor in the opposite coefficient cancels against the length
of the birth direction. The support version keeps the evaluated trace
data explicit; actual seeded words supply them separately. -/

noncomputable section
attribute [-instance] DivisionRing.toRatAlgebra
local instance : Algebra ℚ ℝ := DivisionRing.toRatAlgebra

namespace Markov

/-- The conjugate coefficient pair has the exact logarithmic corner sum. -/
theorem traceCoefficient_conjugate_log_jump (t b c : ℤ) [ht : Fact (3 ≤ t)]
    (hb : 0 < b) (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) :
    2 * Real.log (traceRealEmbedding t (traceCoefficient t b c)) +
      2 * Real.log (traceRealEmbedding t (traceCoefficient t b (t * b - c))) =
      analyticCornerJump t := by
  have hp := traceCoefficient_real_pos t b c hb hf
  have hn : traceRealEmbedding t (traceCoefficient t b c) *
      traceRealEmbedding t (star (traceCoefficient t b c)) =
      (t : ℝ) ^ 2 / ((t : ℝ) ^ 2 - 4) := by
    rw [← traceField_real_norm_eq, traceCoefficient_field_norm t b c ht.out hf]
    push_cast
    rfl
  rw [← traceCoefficient_star t b c ht.out]
  unfold analyticCornerJump
  rw [← hn, Real.log_mul hp.1.ne' hp.2.ne']
  ring

/-- The two expanding birth coefficients have a logarithmic excess
equal to the explicit corner expression. -/
theorem traceCoefficient_birth_log_jump (t a b : ℤ) [ht : Fact (3 ≤ t)]
    (ha : 0 < a) (hf : t ^ 2 + a ^ 2 + b ^ 2 = t * a * b) :
    2 * Real.log (traceRealEmbedding t (traceCoefficient t a (t * a - b))) +
      2 * Real.log (traceRealEmbedding t (traceCoefficient t b (t * b - a))) -
      2 * Real.log (positiveTraceRoot t) = analyticCornerJump t := by
  have hf' : t ^ 2 + a ^ 2 + (t * a - b) ^ 2 = t * a * (t * a - b) := by
    nlinarith [hf]
  have hp := traceCoefficient_real_pos t a (t * a - b) ha hf'
  have hr : 0 < positiveTraceRoot t := by
    linarith [positiveTraceRoot_gt_one t ht.out]
  have hn : traceRealEmbedding t (traceCoefficient t a (t * a - b)) *
      traceRealEmbedding t (star (traceCoefficient t a (t * a - b))) =
      (t : ℝ) ^ 2 / ((t : ℝ) ^ 2 - 4) := by
    rw [← traceField_real_norm_eq, traceCoefficient_field_norm t a (t * a - b) ht.out hf']
    push_cast
    rfl
  rw [traceCoefficient_birth_opposite t a b, map_mul, traceRealEmbedding_root,
    Real.log_mul hr.ne' hp.2.ne']
  unfold analyticCornerJump
  rw [← hn, Real.log_mul hp.1.ne' hp.2.ne']
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two actual birth supports with the trace-ray evaluations have precisely
the logarithmic jump on the common integral partner. -/
theorem birth_norming_support_jump (B : Module.Basis (Fin 2) ℝ E)
    (u v : ℤ × ℤ) (f g : StrongDual ℝ E)
    (hg : g ∈ normingFunctionals (intVector B (u + v)))
    (t a b : ℤ) [ht : Fact (3 ≤ t)] (ha : 0 < a)
    (hf : t ^ 2 + a ^ 2 + b ^ 2 = t * a * b)
    (htrace : (t : ℝ) = 2 * Real.cosh (‖intVector B (u + v)‖ / 2))
    (hfu : f (intVector B u) =
      2 * Real.log (traceRealEmbedding t (traceCoefficient t a (t * a - b))))
    (hgv : g (intVector B v) =
      2 * Real.log (traceRealEmbedding t (traceCoefficient t b (t * b - a)))) :
    f (intVector B u) - g (intVector B u) = analyticCornerJump t := by
  have hself := hg.2
  have hadd : intVector B (u + v) = intVector B u + intVector B v := by
    simp only [intVector, Prod.fst_add, Prod.snd_add, Int.cast_add, add_smul]
    abel
  rw [hadd, map_add, hgv] at hself
  have hlength := traceLength_eq_two_log_root t ht.out
    ‖intVector B (u + v)‖ (norm_nonneg _) htrace
  rw [hadd] at hlength
  have hj := traceCoefficient_birth_log_jump t a b ha hf
  rw [hfu]
  linarith

end Markov
