/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Complex.Basic

namespace RiemannGaussian.ZetaNearOneLocalDisc
noncomputable section


def center (x t : ℝ) : ℂ := ((1 + x : ℝ) : ℂ) + Complex.I * (t : ℂ)

end
end RiemannGaussian.ZetaNearOneLocalDisc

-- Modified from David Sanftenberg’s RiemannGaussian for the Lean 4.28.0 certificate.
