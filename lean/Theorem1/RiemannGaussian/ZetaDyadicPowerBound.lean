/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DirichletDyadicBlocks

namespace RiemannGaussian.ZetaDyadicPowerBound
noncomputable section
open DirichletDyadicBlocks

/-- The trivial estimate keeps the whole real damping of each dyadic
block, rather than bounding its terms merely by one. -/
theorem trivial_block_bound {s : ℂ} (hσ : 0 ≤ s.re) (j : ℕ) :
    ‖block s j‖ ≤ ((2 ^ j : ℕ) : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ (-s.re) := by
  unfold block
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.range (2 ^ j), (((2 ^ j : ℕ) : ℝ) ^ (-s.re)) := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_zetaPrimeFeature, weight_eq_rpow s.re (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity)
        (by exact_mod_cast Nat.le_add_right (2 ^ j) n) (neg_nonpos.mpr hσ)
    _ = _ := by simp

end
end RiemannGaussian.ZetaDyadicPowerBound

-- Modified from David Sanftenberg’s RiemannGaussian for the Lean 4.28.0 certificate.
