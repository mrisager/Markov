import Markov.Arithmetic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The real embedding selecting the expanding root of `X²-tX+1`, and
the multiplicative-independence step in the proof of Lemma 5. -/

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra
local instance : Algebra ℚ ℝ := DivisionRing.toRatAlgebra

namespace Markov

noncomputable def positiveTraceRoot (t : ℤ) : ℝ :=
  ((t : ℝ) + Real.sqrt ((t : ℝ) ^ 2 - 4)) / 2

theorem positiveTraceRoot_equation (t : ℤ) (ht : 3 ≤ t) :
    positiveTraceRoot t ^ 2 - (t : ℝ) * positiveTraceRoot t + 1 = 0 := by
  have ht' : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have hs := Real.sq_sqrt (show 0 ≤ (t : ℝ) ^ 2 - 4 by nlinarith)
  dsimp [positiveTraceRoot]
  nlinarith

theorem positiveTraceRoot_gt_one (t : ℤ) (ht : 3 ≤ t) : 1 < positiveTraceRoot t := by
  have ht' : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have hs := Real.sqrt_nonneg ((t : ℝ) ^ 2 - 4)
  dsimp [positiveTraceRoot]
  linarith

noncomputable def traceRealEmbedding (t : ℤ) [ht : Fact (3 ≤ t)] : TraceField t →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨positiveTraceRoot t, by
    have heq := positiveTraceRoot_equation t ht.out
    simp only [Rat.smul_def, Rat.cast_neg, Rat.cast_one, neg_one_mul, Rat.cast_intCast]
    nlinarith [heq]⟩

theorem traceRealEmbedding_root (t : ℤ) [Fact (3 ≤ t)] :
    traceRealEmbedding t (traceRoot t) = positiveTraceRoot t := by
  simp [traceRealEmbedding, traceRoot]

theorem traceRealEmbedding_injective (t : ℤ) [Fact (3 ≤ t)] :
    Function.Injective (traceRealEmbedding t) := (traceRealEmbedding t).injective

theorem traceRoot_zpow_eq_one (t : ℤ) [ht : Fact (3 ≤ t)] (m : ℤ)
    (hm : traceRoot t ^ m = 1) : m = 0 := by
  have he := congrArg (traceRealEmbedding t) hm
  rw [map_zpow₀, map_one, traceRealEmbedding_root] at he
  have hpos := positiveTraceRoot_gt_one t ht.out
  exact (zpow_eq_one_iff_right₀ (by linarith : 0 ≤ positiveTraceRoot t)
    (ne_of_gt hpos)).mp he

/-- The nonvanishing step in Lemma 5: a unit of norm 1 and a coefficient
of norm greater than 1 cannot have a nontrivial multiplicative relation. -/
theorem trace_multiplicatively_independent (t b c : ℤ) [ht : Fact (3 ≤ t)]
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) (m n : ℤ)
    (hrel : traceRoot t ^ m * traceCoefficient t b c ^ (-n) = 1) :
    m = 0 ∧ n = 0 := by
  have hnorm := congrArg (Algebra.norm ℚ) hrel
  rw [map_mul, map_one,
    map_zpow' (Algebra.norm ℚ) (fun x => Algebra.norm_inv x),
    map_zpow' (Algebra.norm ℚ) (fun x => Algebra.norm_inv x),
    traceRoot_field_norm, one_zpow, one_mul] at hnorm
  have hn0 : -n = 0 := (zpow_eq_one_iff_right₀
    (by linarith [traceCoefficient_field_norm_gt_one t b c ht.out hf])
    (ne_of_gt (traceCoefficient_field_norm_gt_one t b c ht.out hf))).mp hnorm
  have hn : n = 0 := by omega
  subst n
  simp only [neg_zero, zpow_zero, mul_one] at hrel
  exact ⟨traceRoot_zpow_eq_one t m hrel, rfl⟩

theorem trace_beta_ne_one (t b c : ℤ) [Fact (3 ≤ t)]
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) (m n : ℤ)
    (h : m ≠ 0 ∨ n ≠ 0) :
    traceRoot t ^ m * traceCoefficient t b c ^ (-n) ≠ 1 := by
  intro hrel
  obtain ⟨hm, hn⟩ := trace_multiplicatively_independent t b c hf m n hrel
  aesop

end Markov
