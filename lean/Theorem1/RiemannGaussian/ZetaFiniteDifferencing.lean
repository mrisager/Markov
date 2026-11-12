/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.LogarithmicShiftPhase
import RiemannGaussian.ZetaPrimeMomentEnvelope

namespace RiemannGaussian.ZetaFiniteDifferencing
noncomputable section
open Complex LogarithmicShiftPhase

/-- The existing Dirichlet feature has its exact radial-phase split. -/
theorem feature_polar (s : ℂ) (n : ℕ) :
    zetaPrimeFeature s n = (zetaPrimeExpWeight s.re n : ℂ) *
      Complex.exp (((phase s.im (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rw [zetaPrimeFeature, zetaPrimeExpWeight, phase, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp <;> ring

end
end RiemannGaussian.ZetaFiniteDifferencing

-- Modified from David Sanftenberg’s RiemannGaussian for the Lean 4.28.0 certificate.
