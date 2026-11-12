import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! A concrete cubic polynomial factor can be absorbed by halving a positive
exponential decay rate. The estimate holds at every nonnegative real height. -/

namespace Markov

theorem cube_mul_exp_neg_le_half_rate (c H : ℝ) (hc : 0 < c) (hH : 0 ≤ H) :
    H ^ 3 * Real.exp (-c * H) ≤
      (48 / c ^ 3) * Real.exp (-(c / 2) * H) := by
  have hterm := Real.pow_div_factorial_le_exp ((c / 2) * H)
    (show 0 ≤ (c / 2) * H by positivity) 3
  norm_num only [Nat.factorial, Nat.cast_ofNat] at hterm
  have hpoly : H ^ 3 ≤ (48 / c ^ 3) * Real.exp ((c / 2) * H) := by
    calc
      H ^ 3 = (48 / c ^ 3) * (((c / 2) * H) ^ 3 / 6) := by
        field_simp [hc.ne']
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hterm (by positivity)
  calc
    H ^ 3 * Real.exp (-c * H) ≤
        ((48 / c ^ 3) * Real.exp ((c / 2) * H)) * Real.exp (-c * H) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = (48 / c ^ 3) * Real.exp (-(c / 2) * H) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem exists_cube_mul_exp_neg_le_half_rate (c : ℝ) (hc : 0 < c) :
    ∃ M : ℝ, 0 < M ∧ ∀ H : ℝ, 1 ≤ H →
      H ^ 3 * Real.exp (-c * H) ≤ M * Real.exp (-(c / 2) * H) := by
  refine ⟨48 / c ^ 3, by positivity, ?_⟩
  intro H hH
  exact cube_mul_exp_neg_le_half_rate c H hc (by linarith)

end Markov
