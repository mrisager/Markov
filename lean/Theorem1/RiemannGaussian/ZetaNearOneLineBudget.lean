/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaDyadicTruncation
import Mathlib.Analysis.Complex.ExponentialBounds

namespace RiemannGaussian.ZetaNearOneLineBudget
noncomputable section
open ZetaDyadicTruncation

/-- In the closed unit strip at nonnegative height the complex norm
is at most the height plus one. -/
theorem norm_le_height_add_one {s : ℂ} (hσ : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : 0 ≤ s.im) : ‖s‖ ≤ s.im + 1 := by
  have h := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg hσ, abs_of_nonneg ht] at h
  linarith

/-- Every dyadic scale in the canonical eta prefix is at most four
times the height, throughout the closed unit strip above height two. -/
theorem canonical_scale_le {s : ℂ} (hσ : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : 2 ≤ s.im) {j : ℕ} (hj : j ≤ depth s) :
    ((2 ^ j : ℕ) : ℝ) ≤ 4 * s.im := by
  have hn := norm_le_height_add_one hσ hσ1 (by linarith)
  have hd := depth_length_lt s
  have hp : ((2 ^ j : ℕ) : ℝ) ≤ ((2 ^ depth s : ℕ) : ℝ) := by
    exact_mod_cast pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) hj
  linarith

/-- The complete canonical prefix contains at most eight natural
logarithms of the height many blocks. -/
theorem canonical_count_le {s : ℂ} (hσ : 0 ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : 2 ≤ s.im) : ((depth s + 1 : ℕ) : ℝ) ≤ 8 * Real.log s.im := by
  have htpos : 0 < s.im := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht
  have hn := norm_le_height_add_one hσ hσ1 htpos.le
  have hh : ‖s‖ + 2 ≤ 4 * s.im := by linarith
  have hl := Real.log_le_log (by positivity : 0 < ‖s‖ + 2) hh
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat]
      using Real.log_pow (2 : ℝ) 2
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) htpos.ne', hfour] at hl
  have hd := (le_div_iff₀ hl2).mp (depth_le_log s)
  have hc : (((depth s + 1 : ℕ) : ℝ)) * Real.log 2 ≤ 4 * Real.log s.im := by
    push_cast
    nlinarith
  have hb : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ ((depth s + 1 : ℕ) : ℝ) by positivity)
  nlinarith

end
end RiemannGaussian.ZetaNearOneLineBudget

-- Modified from David Sanftenberg’s RiemannGaussian for the Lean 4.28.0 certificate.
