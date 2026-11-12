import Markov.RealEmbedding
import Mathlib.RingTheory.Norm.Transitivity

/-! The integer-norm lower bound used in Lemma 5. These results concern
actual integral elements of the quadratic field, not a postulated norm. -/

noncomputable section
attribute [-instance] DivisionRing.toRatAlgebra
local instance : Algebra ℚ ℝ := DivisionRing.toRatAlgebra

namespace Markov

theorem traceField_integral_norm_is_integer (t : ℤ) [Fact (3 ≤ t)]
    (z : TraceField t) (hz : IsIntegral ℤ z) :
    ∃ n : ℤ, (n : ℚ) = Algebra.norm ℚ z := by
  exact IsIntegrallyClosed.algebraMap_eq_of_integral (Algebra.isIntegral_norm ℚ hz)

theorem traceField_one_le_abs_norm (t : ℤ) [Fact (3 ≤ t)]
    (z : TraceField t) (hz : IsIntegral ℤ z) (hne : z ≠ 0) :
    (1 : ℚ) ≤ |Algebra.norm ℚ z| := by
  obtain ⟨n, hn⟩ := traceField_integral_norm_is_integer t z hz
  have hn0 : n ≠ 0 := by
    intro h
    have hz0 : Algebra.norm ℚ z = 0 := by simpa [h] using hn.symm
    exact hne (Algebra.norm_eq_zero_iff.mp hz0)
  rw [← hn]
  exact_mod_cast (Int.one_le_abs hn0)

theorem traceField_real_norm_eq (t : ℤ) [Fact (3 ≤ t)] (z : TraceField t) :
    (Algebra.norm ℚ z : ℝ) =
      traceRealEmbedding t z * traceRealEmbedding t (star z) := by
  have h := congrArg (traceRealEmbedding t)
    (QuadraticAlgebra.algebraMap_norm_eq_mul_star z)
  rw [map_mul, (traceRealEmbedding t).commutes] at h
  simpa [traceField_norm_eq] using h

/-- Both real conjugates of `A` are positive when the sum `b` is positive. -/
theorem traceCoefficient_real_pos (t b c : ℤ) [ht : Fact (3 ≤ t)] (hb : 0 < b)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) :
    0 < traceRealEmbedding t (traceCoefficient t b c) ∧
      0 < traceRealEmbedding t (star (traceCoefficient t b c)) := by
  have hn : (0 : ℝ) < (Algebra.norm ℚ (traceCoefficient t b c) : ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : (0 : ℚ) < 1)
      (traceCoefficient_field_norm_gt_one t b c ht.out hf))
  rw [traceField_real_norm_eq] at hn
  have hs := congrArg (traceRealEmbedding t) (traceCoefficient_add_star t b c ht.out)
  simp only [map_add, map_intCast] at hs
  rcases mul_pos_iff.mp hn with h | h
  · exact h
  · have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    exfalso
    linarith [h.1, h.2]

/-- The lower bound arising from a nonzero integral norm. -/
theorem traceField_one_le_product_embeddings (t : ℤ) [Fact (3 ≤ t)]
    (z : TraceField t) (hz : IsIntegral ℤ z) (hne : z ≠ 0) :
    1 ≤ |traceRealEmbedding t z| * |traceRealEmbedding t (star z)| := by
  have hq := traceField_one_le_abs_norm t z hz hne
  have hr : (1 : ℝ) ≤ |(Algebra.norm ℚ z : ℝ)| := by exact_mod_cast hq
  rwa [traceField_real_norm_eq, abs_mul] at hr

/-- All integral powers of the distinguished unit remain algebraic integers. -/
theorem traceRoot_zpow_isIntegral (t : ℤ) [Fact (3 ≤ t)] (m : ℤ) :
    IsIntegral ℤ (traceRoot t ^ m) := by
  cases m with
  | ofNat k => simpa using (traceRoot_isIntegral t).pow k
  | negSucc k =>
    rw [zpow_negSucc, ← inv_pow, ← traceRoot_star_eq_inv]
    exact (traceRoot_star_isIntegral t).pow (k + 1)

end Markov
