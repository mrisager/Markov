/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaNearOneBudgetLimit

namespace RiemannGaussian.ZetaLogLogBudget
noncomputable section
open ZetaNearOneBudgetLimit ZetaNearOneLogProfile

theorem scale_double_bounds (t : ℝ) :
    scale t ≤ scale (2 * t) ∧ scale (2 * t) ≤ 2 * scale t := by
  have hl : Real.log 2 ≤ scale t := Real.log_le_log (by norm_num) (two_le_height t)
  have hlo : height t ≤ height (2 * t) := by
    simp only [height, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg t]
  have hhi : height (2 * t) ≤ 2 * height t := by
    simp only [height, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have h := Real.log_le_log (by linarith [two_le_height (2 * t)] : 0 < height (2 * t)) hhi
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by linarith [two_le_height t] : height t ≠ 0)] at h
  refine ⟨Real.log_le_log (by linarith [two_le_height t]) hlo, ?_⟩
  change scale (2 * t) ≤ Real.log 2 + scale t at h
  linarith

end
end RiemannGaussian.ZetaLogLogBudget

-- Modified from David Sanftenberg’s RiemannGaussian for the Lean 4.28.0 certificate.
