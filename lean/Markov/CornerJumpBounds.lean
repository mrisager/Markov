import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Analytic lower bounds for the logarithmic corner expression from Theorem 2.
The identification of this expression with a geometric corner jump is a
separate input; this module only proves inequalities for real traces. -/

noncomputable section

namespace Markov

/-- The real logarithmic expression occurring in the corner formula. -/
def analyticCornerJump (t : ℝ) : ℝ :=
  2 * Real.log (t ^ 2 / (t ^ 2 - 4))

/-- The elementary lower bound for the logarithmic corner expression. -/
theorem analyticCornerJump_ge_eight_div_sq (t : ℝ) (ht : 3 ≤ t) :
    8 / t ^ 2 ≤ analyticCornerJump t := by
  have ht0 : 0 < t := by linarith
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht0
  have hd : 0 < t ^ 2 - 4 := by nlinarith
  have hq : 0 < t ^ 2 / (t ^ 2 - 4) := div_pos ht2 hd
  have hlog : 4 / t ^ 2 ≤ Real.log (t ^ 2 / (t ^ 2 - 4)) := by
    calc
      _ = 1 - (t ^ 2 / (t ^ 2 - 4))⁻¹ := by
        field_simp
        ring
      _ ≤ _ := Real.one_sub_inv_le_log_of_pos hq
  unfold analyticCornerJump
  calc
    8 / t ^ 2 = 2 * (4 / t ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by norm_num)

/-- Every real trace at least three gives a strictly positive expression. -/
theorem analyticCornerJump_pos (t : ℝ) (ht : 3 ≤ t) :
    0 < analyticCornerJump t := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos (by linarith : 0 < t)
  exact (div_pos (by norm_num : (0 : ℝ) < 8) ht2).trans_le
    (analyticCornerJump_ge_eight_div_sq t ht)

/-- A trace upper bound gives an exponential lower bound for the expression.
The length and its relation to the real trace are explicit hypotheses. -/
theorem analyticCornerJump_ge_two_exp_neg (t ℓ : ℝ) (ht : 3 ≤ t)
    (htrace : t ≤ 2 * Real.exp (ℓ / 2)) :
    2 * Real.exp (-ℓ) ≤ analyticCornerJump t := by
  have ht0 : 0 < t := by linarith
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht0
  have hs : t ^ 2 ≤ (2 * Real.exp (ℓ / 2)) ^ 2 := by
    nlinarith [Real.exp_pos (ℓ / 2)]
  have he : Real.exp (-ℓ) * Real.exp (ℓ / 2) ^ 2 = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hb : 2 * Real.exp (-ℓ) ≤ 8 / t ^ 2 := by
    apply (le_div_iff₀ ht2).mpr
    have hm := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-ℓ)).le
    nlinarith
  exact hb.trans (analyticCornerJump_ge_eight_div_sq t ht)

/-- The usual nonnegative trace--length relation supplies the trace upper bound. -/
theorem analyticCornerJump_ge_two_exp_neg_of_cosh (t ℓ : ℝ) (ht : 3 ≤ t)
    (hℓ : 0 ≤ ℓ) (htrace : t = 2 * Real.cosh (ℓ / 2)) :
    2 * Real.exp (-ℓ) ≤ analyticCornerJump t := by
  apply analyticCornerJump_ge_two_exp_neg t ℓ ht
  have he : Real.exp (-(ℓ / 2)) ≤ Real.exp (ℓ / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [htrace, Real.cosh_eq]
  linarith

end Markov
