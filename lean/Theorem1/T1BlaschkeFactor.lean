import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-! Actual finite Blaschke factors for the local zeta zero detector. -/

namespace Markov
open Complex
open scoped ComplexConjugate
noncomputable section

/-- The denominator of the disk factor at a zero a. -/
def t1_blaschkeDenom (r : ℝ) (a z : ℂ) : ℂ :=
  (r : ℂ)^2 - conj a * z

/-- The factor vanishes at a and has unit norm on the radius-r sphere. -/
def t1_blaschkeFactor (r : ℝ) (a z : ℂ) : ℂ :=
  (r : ℂ) * (z-a) / t1_blaschkeDenom r a z

theorem t1_blaschkeDenom_ne_zero {r : ℝ} (hr : 0 < r) {a z : ℂ}
    (ha : ‖a‖ < r) (hz : ‖z‖ ≤ r) : t1_blaschkeDenom r a z ≠ 0 := by
  intro h
  have he := congrArg norm (sub_eq_zero.mp h)
  change ‖(r : ℂ)^2‖ = ‖conj a * z‖ at he
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le, norm_mul,
    Complex.norm_conj] at he
  have hlt := (mul_le_mul_of_nonneg_left hz (norm_nonneg a)).trans_lt
    (mul_lt_mul_of_pos_right ha hr)
  nlinarith

theorem t1_blaschkeFactor_analyticAt {r : ℝ} (hr : 0 < r) {a z : ℂ}
    (ha : ‖a‖ < r) (hz : ‖z‖ ≤ r) :
    AnalyticAt ℂ (t1_blaschkeFactor r a) z := by
  unfold t1_blaschkeFactor
  refine AnalyticAt.div (by fun_prop) ?_ (t1_blaschkeDenom_ne_zero hr ha hz)
  unfold t1_blaschkeDenom
  fun_prop

theorem t1_blaschkeFactor_ne_zero {r : ℝ} (hr : 0 < r) {a z : ℂ}
    (ha : ‖a‖ < r) (hz : ‖z‖ ≤ r) (hza : z ≠ a) :
    t1_blaschkeFactor r a z ≠ 0 := by
  unfold t1_blaschkeFactor
  exact div_ne_zero (mul_ne_zero (by exact_mod_cast hr.ne') (sub_ne_zero.mpr hza))
    (t1_blaschkeDenom_ne_zero hr ha hz)

theorem t1_norm_blaschkeFactor_boundary {r : ℝ} (hr : 0 < r) {a z : ℂ}
    (ha : ‖a‖ < r) (hz : ‖z‖ = r) : ‖t1_blaschkeFactor r a z‖ = 1 := by
  have hsq : ‖t1_blaschkeDenom r a z‖^2 = (r * ‖z-a‖)^2 := by
    have hz' : z.re*z.re + z.im*z.im = r^2 := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]
    simp only [t1_blaschkeDenom, mul_pow, Complex.sq_norm, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, ← Complex.ofReal_pow,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    linear_combination (a.re*a.re + a.im*a.im - r^2) * hz'
  have he : ‖t1_blaschkeDenom r a z‖ = r * ‖z-a‖ := by
    have hab := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
    simpa only [abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (mul_nonneg hr.le (norm_nonneg _))] using hab
  have hn := norm_ne_zero_iff.mpr (t1_blaschkeDenom_ne_zero hr ha hz.le)
  rw [t1_blaschkeFactor, norm_div, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hr.le, ← he, div_self hn]

theorem t1_norm_blaschkeFactor_zero {r : ℝ} (hr : 0 < r) (a : ℂ) :
    ‖t1_blaschkeFactor r a 0‖ = ‖a‖ / r := by
  rw [t1_blaschkeFactor, t1_blaschkeDenom, mul_zero, sub_zero, zero_sub,
    norm_div, norm_mul, norm_neg, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hr.le]
  field_simp

theorem t1_logDeriv_blaschkeFactor_zero {r : ℝ} (hr : 0 < r) {a : ℂ}
    (ha : ‖a‖ < r) (ha0 : a ≠ 0) :
    logDeriv (t1_blaschkeFactor r a) 0 = -1/a + conj a / (r : ℂ)^2 := by
  have hn : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hnum : HasDerivAt (fun z : ℂ => (r : ℂ) * (z-a)) (r : ℂ) 0 := by
    simpa only [mul_one] using ((hasDerivAt_id (0 : ℂ)).sub_const a).const_mul (r : ℂ)
  have hden : HasDerivAt (t1_blaschkeDenom r a) (-conj a) 0 := by
    unfold t1_blaschkeDenom
    simpa only [mul_one] using
      ((hasDerivAt_id (0 : ℂ)).const_mul (conj a)).const_sub ((r : ℂ)^2)
  have h0 : (fun z : ℂ => (r : ℂ) * (z-a)) 0 ≠ 0 :=
    mul_ne_zero hn (sub_ne_zero.mpr (Ne.symm ha0))
  unfold t1_blaschkeFactor
  rw [logDeriv_div 0 h0 (t1_blaschkeDenom_ne_zero hr ha (by simpa using hr.le))
      hnum.differentiableAt hden.differentiableAt,
    logDeriv_apply, logDeriv_apply, hnum.deriv, hden.deriv]
  simp only [zero_sub, t1_blaschkeDenom, mul_zero, sub_zero]
  field_simp
  ring

end
end Markov
