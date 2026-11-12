/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace RiemannGaussian.ZetaNearOneLogProfile
noncomputable section


def height (y : ℝ) : ℝ := |y| + 2

/-- The enlarged height is always at least two. -/
theorem two_le_height (y : ℝ) : 2 ≤ height y := by unfold height; linarith [abs_nonneg y]

end
end RiemannGaussian.ZetaNearOneLogProfile

-- Modified from David Sanftenberg’s RiemannGaussian for the Lean 4.28.0 certificate.
