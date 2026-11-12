/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DirichletDyadicBlocks
import Mathlib.Data.Nat.Log

namespace RiemannGaussian.ZetaDyadicTruncation

/-- A canonical logarithmic block depth, large enough for the actual
height-uniform eta tail estimate. -/
noncomputable def depth (s : ℂ) : ℕ := Nat.log 2 (⌈‖s‖⌉₊ + 1)

/-- The canonical logarithmic depth satisfies the actual tail-scale
condition at every complex argument. -/
theorem depth_scale (s : ℂ) : ‖s‖ ≤ ((2 * 2 ^ depth s + 1 : ℕ) : ℝ) := by
  have hc := Nat.le_ceil ‖s‖
  have hp := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (⌈‖s‖⌉₊ + 1)
  rw [Nat.succ_eq_add_one, pow_succ] at hp
  have hr : ((⌈‖s‖⌉₊ + 1 : ℕ) : ℝ) < ((2 : ℕ) ^ depth s * 2 : ℕ) := by
    exact_mod_cast hp
  push_cast at hr ⊢
  nlinarith

/-- The canonical dyadic cutoff stays below the argument norm plus two,
so its number of blocks is genuinely logarithmic in height. -/
theorem depth_length_lt (s : ℂ) : ((2 ^ depth s : ℕ) : ℝ) < ‖s‖ + 2 := by
  have hp := Nat.pow_log_le_self 2 (show ⌈‖s‖⌉₊ + 1 ≠ 0 by omega)
  have hr : ((2 ^ depth s : ℕ) : ℝ) ≤ ((⌈‖s‖⌉₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast hp
  have hc := Nat.ceil_lt_add_one (norm_nonneg s)
  push_cast at hr ⊢
  linarith

/-- An explicit real logarithmic bound for the canonical number of
dyadic blocks, uniform over all complex arguments. -/
theorem depth_le_log (s : ℂ) : (depth s : ℝ) ≤ Real.log (‖s‖ + 2) / Real.log 2 := by
  have hp : (2 : ℝ) ^ depth s ≤ ‖s‖ + 2 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (depth_length_lt s).le
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ depth s) hp
  rw [Real.log_pow] at hl
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hl


end RiemannGaussian.ZetaDyadicTruncation

-- Modified from David Sanftenberg’s RiemannGaussian for the Lean 4.28.0 certificate.
