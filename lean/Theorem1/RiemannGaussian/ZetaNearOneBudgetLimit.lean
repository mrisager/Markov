/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaNearOneLogProfile
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace RiemannGaussian.ZetaNearOneBudgetLimit
noncomputable section
open Filter ZetaNearOneLogProfile
open scoped Topology

def scale (t : ℝ) : ℝ := Real.log (height t)

/-- The logarithmic height never vanishes. -/
theorem scale_pos (t : ℝ) : 0 < scale t :=
  Real.log_pos (by linarith [two_le_height t])

/-- The actual logarithmic height tends to infinity. -/
theorem scale_atTop : Tendsto scale atTop atTop :=
  Real.tendsto_log_atTop.comp
    (tendsto_atTop_mono (fun t : ℝ ↦ show t ≤ |t| + 2 by linarith [le_abs_self t]) tendsto_id)

end
end RiemannGaussian.ZetaNearOneBudgetLimit

-- Modified from David Sanftenberg’s RiemannGaussian for the Lean 4.28.0 certificate.
