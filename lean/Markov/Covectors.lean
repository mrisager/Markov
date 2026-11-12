import Markov.SeparationBounds

/-! Integral covector evaluations and the logarithmic linear form of v1 Lemma 5. -/

noncomputable section
attribute [-instance] DivisionRing.toRatAlgebra
local instance : Algebra ℚ ℝ := DivisionRing.toRatAlgebra

namespace Markov

def intDet (u v : ℤ × ℤ) : ℤ := u.1 * v.2 - u.2 * v.1

def intEval (d u : ℤ × ℤ) : ℤ := d.1 * u.1 + d.2 * u.2

theorem intCovector_evals_nonzero (u v d : ℤ × ℤ)
    (hdet : intDet u v ≠ 0) (hd : d ≠ (0, 0)) :
    intEval d v ≠ 0 ∨ intEval d u ≠ 0 := by
  by_contra h
  push_neg at h
  have h₀ : d.1 * intDet u v = 0 := by
    dsimp [intDet, intEval] at *
    linear_combination v.2 * h.2 - u.2 * h.1
  have h₁ : d.2 * intDet u v = 0 := by
    dsimp [intDet, intEval] at *
    linear_combination u.1 * h.1 - v.1 * h.2
  exact hd (Prod.ext ((mul_eq_zero.mp h₀).resolve_right hdet)
    ((mul_eq_zero.mp h₁).resolve_right hdet))

/-- The logarithmic identity appearing in the determinant calculation. -/
theorem trace_beta_log_identity (t b c : ℤ) [ht : Fact (3 ≤ t)]
    (hb : 0 < b) (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) (m n : ℤ) :
    Real.log (traceRealEmbedding t (traceRoot t ^ m * traceCoefficient t b c ^ (-n))) =
      (m : ℝ) * Real.log (positiveTraceRoot t) -
        (n : ℝ) * Real.log (traceRealEmbedding t (traceCoefficient t b c)) := by
  have hr : positiveTraceRoot t ≠ 0 := ne_of_gt (by linarith [positiveTraceRoot_gt_one t ht.out])
  have hA := ne_of_gt (traceCoefficient_real_pos t b c hb hf).1
  rw [map_mul, map_zpow₀, map_zpow₀, traceRealEmbedding_root,
    Real.log_mul (zpow_ne_zero m hr) (zpow_ne_zero (-n) hA),
    Real.log_zpow, Real.log_zpow]
  push_cast
  ring

theorem trace_log_linear_form_ne_zero (t b c : ℤ) [ht : Fact (3 ≤ t)]
    (hb : 0 < b) (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) (m n : ℤ)
    (hexp : m ≠ 0 ∨ n ≠ 0) :
    2 * Real.log (positiveTraceRoot t) * (m : ℝ) -
      2 * Real.log (traceRealEmbedding t (traceCoefficient t b c)) * (n : ℝ) ≠ 0 := by
  intro hzero
  let β := traceRoot t ^ m * traceCoefficient t b c ^ (-n)
  have hlog : Real.log (traceRealEmbedding t β) = 0 := by
    rw [trace_beta_log_identity t b c hb hf]
    linarith
  have hp : 0 < traceRealEmbedding t β := by
    dsimp [β]
    rw [map_mul, map_zpow₀, map_zpow₀, traceRealEmbedding_root]
    exact mul_pos (zpow_pos (by linarith [positiveTraceRoot_gt_one t ht.out]) _)
      (zpow_pos (traceCoefficient_real_pos t b c hb hf).1 _)
  have heq : traceRealEmbedding t β = 1 := by
    rw [← Real.exp_log hp, hlog, Real.exp_zero]
  apply trace_beta_ne_one t b c hf m n hexp
  apply traceRealEmbedding_injective t
  simpa [β] using heq

/-- Nonzero integral covectors produce nonzero logarithmic linear forms. -/
theorem trace_covector_linear_form_ne_zero (t b c : ℤ) [Fact (3 ≤ t)]
    (hb : 0 < b) (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c)
    (u v d : ℤ × ℤ) (hdet : intDet u v ≠ 0) (hd : d ≠ (0, 0)) :
    2 * Real.log (positiveTraceRoot t) * (intEval d v : ℝ) -
      2 * Real.log (traceRealEmbedding t (traceCoefficient t b c)) * (intEval d u : ℝ) ≠ 0 :=
  trace_log_linear_form_ne_zero t b c hb hf _ _ (intCovector_evals_nonzero u v d hdet hd)

end Markov
