import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Fourier.FourierTransform

/-! The elementary oscillatory interval bound used by line slicing to
control the Fourier transform of a convex body's indicator. -/

open Set MeasureTheory
namespace Markov

/-- Exact integration of a nonconstant imaginary exponential gives a bound
independent of the interval length and its endpoints. -/
theorem norm_integral_exp_imaginary_le (r a b : ℝ) (hr : r ≠ 0) :
    ‖∫ x : ℝ in a..b, Complex.exp (((r : ℂ) * Complex.I) * x)‖ ≤ 2 / |r| := by
  have hc : (r : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hr) Complex.I_ne_zero
  rw [integral_exp_mul_complex hc, norm_div]
  have hn (x : ℝ) : ‖Complex.exp (((r : ℂ) * Complex.I) * x)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hs : ‖Complex.exp (((r : ℂ) * Complex.I) * b) -
      Complex.exp (((r : ℂ) * Complex.I) * a)‖ ≤ 2 := by
    have hh := norm_sub_le (Complex.exp (((r : ℂ) * Complex.I) * b))
      (Complex.exp (((r : ℂ) * Complex.I) * a))
    simpa only [hn, one_add_one_eq_two] using hh
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] using
    div_le_div_of_nonneg_right hs (norm_nonneg ((r : ℂ) * Complex.I))

/-- The same estimate for the actual set integral of a closed interval. -/
theorem norm_setIntegral_Icc_exp_imaginary_le (r a b : ℝ) (hr : r ≠ 0)
    (hab : a ≤ b) :
    ‖∫ x : ℝ in Icc a b, Complex.exp (((r : ℂ) * Complex.I) * x)‖ ≤ 2 / |r| := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact norm_integral_exp_imaginary_le r a b hr

/-- The Fourier convention is exp(-2π i r x), with no hidden normalization. -/
theorem norm_setIntegral_Icc_fourierChar_le (r a b : ℝ) (hr : r ≠ 0)
    (hab : a ≤ b) :
    ‖∫ x : ℝ in Icc a b, (Real.fourierChar (-(r * x)) : ℂ)‖ ≤
      1 / (Real.pi * |r|) := by
  have hc : -(2 * Real.pi * r) ≠ 0 := neg_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hr)
  have hid : (fun x : ℝ => (Real.fourierChar (-(r * x)) : ℂ)) =
      fun x : ℝ => Complex.exp ((((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I) * x) := by
    funext x
    rw [Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  rw [hid]
  have hh := norm_setIntegral_Icc_exp_imaginary_le (-(2 * Real.pi * r)) a b hc hab
  have heq : 2 / |-(2 * Real.pi * r)| = 1 / (Real.pi * |r|) := by
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos]
    field_simp
  simpa only [heq] using hh

end Markov
