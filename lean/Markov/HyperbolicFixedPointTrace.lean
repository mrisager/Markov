import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Tactic

/-! Fixed points of the actual special-linear action on the upper half-plane.
The trace bound and equality case follow from the fractional-linear formula. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- An interior fixed point gives the exact discriminant identity, with
the strictly positive imaginary coordinate retained. -/
theorem sl_fixed_point_trace_identity (g : SL(2, ℝ)) (z : UpperHalfPlane)
    (hz : g • z = z) :
    (g : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 =
      4 - 4 * (g 1 0) ^ 2 * z.im ^ 2 := by
  let a := g 0 0
  let b := g 0 1
  let c := g 1 0
  let d := g 1 1
  have hdet : a * d - b * c = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hden : (c : ℂ) * (z : ℂ) + (d : ℂ) ≠ 0 := by
    intro hh
    have hi := congrArg Complex.im hh
    have hr := congrArg Complex.re hh
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] at hi
    have hc : c = 0 := (mul_eq_zero.mp hi).resolve_right z.im_ne_zero
    simp only [hc, Complex.ofReal_zero, zero_mul, zero_add] at hr
    have hd : d = 0 := by simpa using hr
    rw [hc, hd] at hdet
    norm_num at hdet
  have heq : (a : ℂ) * (z : ℂ) + (b : ℂ) =
      (z : ℂ) * ((c : ℂ) * z + (d : ℂ)) := by
    have hh := congrArg (fun w : UpperHalfPlane => (w : ℂ)) hz
    change ((g • z : UpperHalfPlane) : ℂ) = (z : ℂ) at hh
    rw [UpperHalfPlane.coe_specialLinearGroup_apply] at hh
    have hh' : ((a : ℂ) * (z : ℂ) + (b : ℂ)) /
        ((c : ℂ) * z + (d : ℂ)) = (z : ℂ) := by simpa only using hh
    exact (div_eq_iff hden).mp hh'
  have hi := congrArg Complex.im heq
  have hr := congrArg Complex.re heq
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.mul_re, zero_mul, add_zero, sub_zero] at hi hr
  change a * z.im = z.re * (c * z.im) + z.im * (c * z.re + d) at hi
  change a * z.re + b = z.re * (c * z.re + d) - z.im * (c * z.im) at hr
  have hprod : (a - d - 2 * c * z.re) * z.im = 0 := by nlinarith [hi]
  have had : a - d = 2 * c * z.re := by
    have hh := (mul_eq_zero.mp hprod).resolve_right z.im_ne_zero
    linarith
  have hb : b = -c * (z.re ^ 2 + z.im ^ 2) := by
    have hh := congrArg (fun t : ℝ => t * z.re) had
    change (a - d) * z.re = (2 * c * z.re) * z.re at hh
    nlinarith [hr]
  have htr : (g : Matrix (Fin 2) (Fin 2) ℝ).trace = a + d := by
    simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, a, d]
  rw [htr]
  change (a + d) ^ 2 = 4 - 4 * c ^ 2 * z.im ^ 2
  calc
    _ = 4 * (a * d - b * c) + (a - d) ^ 2 + 4 * b * c := by ring
    _ = _ := by rw [hdet, had, hb]; ring

/-- A non-elliptic special-linear element can fix an interior point only
in the scalar equality case. -/
theorem sl_fixed_point_trace_sq_le_four (g : SL(2, ℝ)) (z : UpperHalfPlane)
    (hz : g • z = z) : (g : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 ≤ 4 := by
  rw [sl_fixed_point_trace_identity g z hz]
  have hh := mul_nonneg (sq_nonneg (g 1 0)) (sq_nonneg z.im)
  nlinarith

theorem sl_fixed_point_eq_one_or_neg_one_of_trace_sq_eq_four
    (g : SL(2, ℝ)) (z : UpperHalfPlane) (hz : g • z = z)
    (ht : (g : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 = 4) : g = 1 ∨ g = -1 := by
  have hid := sl_fixed_point_trace_identity g z hz
  have hcy : (g 1 0 * z.im) ^ 2 = 0 := by nlinarith [hid]
  have hc : g 1 0 = 0 :=
    (mul_eq_zero.mp (sq_eq_zero_iff.mp hcy)).resolve_right z.im_ne_zero
  have hfix := congrArg (fun w : UpperHalfPlane => (w : ℂ)) hz
  change ((g • z : UpperHalfPlane) : ℂ) = (z : ℂ) at hfix
  rw [UpperHalfPlane.coe_specialLinearGroup_apply] at hfix
  have hdet : g 0 0 * g 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using g.property
  have hd : g 1 1 ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hdet
    norm_num at hdet
  have heq : (g 0 0 : ℂ) * (z : ℂ) + (g 0 1 : ℂ) = (z : ℂ) * (g 1 1 : ℂ) := by
    have hh : ((g 0 0 : ℂ) * (z : ℂ) + (g 0 1 : ℂ)) / (g 1 1 : ℂ) = z := by
      simpa only [hc, map_zero, Complex.ofReal_zero, zero_mul, zero_add] using hfix
    exact (div_eq_iff (by exact_mod_cast hd)).mp hh
  have hi := congrArg Complex.im heq
  have hr := congrArg Complex.re heq
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.mul_re, zero_mul, zero_add, add_zero, sub_zero, mul_zero] at hi hr
  change g 0 0 * z.im = z.im * g 1 1 at hi
  change g 0 0 * z.re + g 0 1 = z.re * g 1 1 at hr
  have ha : g 0 0 = g 1 1 := by
    have hh : (g 0 0 - g 1 1) * z.im = 0 := by nlinarith [hi]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right z.im_ne_zero)
  have hb : g 0 1 = 0 := by rw [ha] at hr; linarith
  have hs : g 1 1 ^ 2 = 1 := by rw [ha] at hdet; nlinarith
  rcases (sq_eq_one_iff).mp hs with hd1 | hdn1
  · left
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd1]
  · right
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hdn1]

end Markov
