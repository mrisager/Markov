/-
Selected proof from David Sanftenberg's RiemannGaussian project,
commit f5fd3ddb407972f9ca65298fbe9be3225fe06635, Apache 2.0.
This port keeps the positive-axis complex-power bound needed by
ordinary Euler truncation; unrelated midpoint and divisor-weight
theorems and imports are omitted.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Complex Set
namespace RiemannGaussian
noncomputable section

/-- Complex powers have an explicit Lipschitz bound above a positive
real base when the real exponent is at most one. -/
theorem norm_cpow_sub_cpow_le_above (r : ℂ) {a x y : ℝ} (ha : 0 < a)
    (hr : r.re ≤ 1) (hx : a ≤ x) (hy : a ≤ y) :
    ‖(y : ℂ) ^ r - (x : ℂ) ^ r‖ ≤ ‖r‖ * a ^ (r.re - 1) * |y - x| := by
  have hderiv (z : ℝ) (hz : z ∈ Ici a) :
      HasDerivWithinAt (fun t : ℝ ↦ (t : ℂ) ^ r)
        (r * (z : ℂ) ^ (r - 1)) (Ici a) z := by
    by_cases hr0 : r = 0
    · subst r
      simpa using (hasDerivAt_const (x := z) (c := (1 : ℂ))).hasDerivWithinAt
    · exact (hasDerivAt_ofReal_cpow_const (ne_of_gt (ha.trans_le hz)) hr0).hasDerivWithinAt
  have hbound (z : ℝ) (hz : z ∈ Ici a) :
      ‖r * (z : ℂ) ^ (r - 1)‖ ≤ ‖r‖ * a ^ (r.re - 1) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hz)]
    simp only [Complex.sub_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hz (by linarith))
      (norm_nonneg _)
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Ici a) hx hy

end
end RiemannGaussian

-- Modified from David Sanftenberg’s RiemannGaussian for the Lean 4.28.0 certificate.
