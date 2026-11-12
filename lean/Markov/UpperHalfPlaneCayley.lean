import Markov.HyperbolicTranslationLength
import Mathlib.Tactic

noncomputable section
open Filter Topology
namespace Markov

/-- The literal complex Cayley map on the actual upper half-plane. -/
def upperHalfPlaneCayley (z : UpperHalfPlane) : ℂ :=
  ((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)

theorem upperHalfPlaneCayley_den_ne_zero (z : UpperHalfPlane) :
    (z : ℂ) + Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, UpperHalfPlane.coe_im, Complex.I_im,
    Complex.zero_im] at hi
  linarith [z.im_pos]

theorem continuous_upperHalfPlaneCayley : Continuous upperHalfPlaneCayley := by
  exact (UpperHalfPlane.continuous_coe.sub continuous_const).div
    (UpperHalfPlane.continuous_coe.add continuous_const)
    upperHalfPlaneCayley_den_ne_zero

theorem upperHalfPlaneCayley_norm_lt_one (z : UpperHalfPlane) :
    ‖upperHalfPlaneCayley z‖ < 1 := by
  have hp : 0 < ‖(z : ℂ) + Complex.I‖ :=
    norm_pos_iff.mpr (upperHalfPlaneCayley_den_ne_zero z)
  rw [upperHalfPlaneCayley, norm_div, div_lt_one hp]
  have hsq : ‖(z : ℂ) - Complex.I‖ ^ 2 < ‖(z : ℂ) + Complex.I‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im, Complex.I_re, Complex.I_im, sub_zero, add_zero]
    nlinarith [z.im_pos]
  nlinarith [norm_nonneg ((z : ℂ) - Complex.I),
    norm_nonneg ((z : ℂ) + Complex.I)]

theorem upperHalfPlaneCayley_add_one (z : UpperHalfPlane) :
    upperHalfPlaneCayley z + 1 = (2 * (z : ℂ)) / ((z : ℂ) + Complex.I) := by
  unfold upperHalfPlaneCayley
  field_simp [upperHalfPlaneCayley_den_ne_zero z]
  ring

theorem upperHalfPlaneCayley_sub_one (z : UpperHalfPlane) :
    upperHalfPlaneCayley z - 1 = (-2 * Complex.I) / ((z : ℂ) + Complex.I) := by
  unfold upperHalfPlaneCayley
  field_simp [upperHalfPlaneCayley_den_ne_zero z]
  ring

theorem upperHalfPlaneCayley_den_norm_lower (z : UpperHalfPlane) :
    z.im + 1 ≤ ‖(z : ℂ) + Complex.I‖ := by
  simpa only [Complex.add_im, UpperHalfPlane.coe_im, Complex.I_im] using
    Complex.im_le_norm ((z : ℂ) + Complex.I)

theorem upperHalfPlaneCayley_norm_add_one_le (z : UpperHalfPlane) :
    ‖upperHalfPlaneCayley z + 1‖ ≤ 2 * ‖(z : ℂ)‖ := by
  rw [upperHalfPlaneCayley_add_one, norm_div, norm_mul]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ (norm_pos_iff.mpr (upperHalfPlaneCayley_den_ne_zero z))).2
  have hden := upperHalfPlaneCayley_den_norm_lower z
  nlinarith [z.im_pos, norm_nonneg (z : ℂ)]

theorem upperHalfPlaneCayley_norm_sub_one_le (z : UpperHalfPlane) :
    ‖upperHalfPlaneCayley z - 1‖ ≤ 2 / (z.im + 1) := by
  rw [upperHalfPlaneCayley_sub_one, norm_div, norm_mul]
  norm_num only [norm_neg, Complex.norm_ofNat, Complex.norm_I, mul_one]
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith [z.im_pos])
    (upperHalfPlaneCayley_den_norm_lower z)

end Markov
