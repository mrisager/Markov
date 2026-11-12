import T1RieszMertensSum
import T1ReciprocalZeta
import Mathlib.NumberTheory.LSeries.Deriv

/-! Each term of the actual Möbius Dirichlet series on the line Re=2
has an absolutely integrable Riesz-weighted kernel. -/
noncomputable section
open Complex MeasureTheory ArithmeticFunction
open scoped Moebius
namespace Markov

def t1_rieszLineTerm (k : ℕ) (x : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (x : ℂ)^(t1_verticalPoint 2 t) *
    LSeries.term (fun m => (μ m : ℂ)) (t1_verticalPoint 2 t) n *
    (t1_rieszDenom k (t1_verticalPoint 2 t))⁻¹

theorem t1_rieszLineTerm_norm (k : ℕ) {x : ℝ} (hx : 0 < x) (n : ℕ) (t : ℝ) :
    ‖t1_rieszLineTerm k x n t‖ =
      (x^2*‖LSeries.term (fun m => (μ m : ℂ)) 2 n‖)*
      ‖(t1_rieszDenom k (t1_verticalPoint 2 t))⁻¹‖ := by
  simp only [t1_rieszLineTerm,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,
    LSeries.norm_term_eq,t1_verticalPoint_re,show (2 : ℂ).re=2 by norm_num,Real.rpow_two]

theorem t1_rieszLineTerm_integrable {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Integrable (t1_rieszLineTerm k x n) := by
  have hV := t1_verticalPoint_continuous 2
  have hden : Continuous (fun t => (t1_rieszDenom k (t1_verticalPoint 2 t))⁻¹) :=
    ((t1_rieszDenom_differentiable k).continuous.comp hV).inv₀ (fun t =>
      t1_rieszDenom_ne_zero k (by rw [t1_verticalPoint_re]; norm_num))
  have hterm : Continuous (fun s => LSeries.term (fun m => (μ m : ℂ)) s n) :=
    (show Differentiable ℂ (fun s => LSeries.term (fun m => (μ m : ℂ)) s n)
      from fun s => (LSeries.hasDerivAt_term _ n s).differentiableAt).continuous
  have hp : Continuous (fun t => (x : ℂ)^(t1_verticalPoint 2 t)) :=
    (continuous_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).comp hV
  have hc : Continuous (t1_rieszLineTerm k x n) := (hp.mul (hterm.comp hV)).mul hden
  have hi := t1_rieszDenom_inv_verticalIntegrable hk (σ := 2) (by norm_num)
  change Integrable (fun t => (t1_rieszDenom k (t1_verticalPoint 2 t))⁻¹) at hi
  exact (hi.norm.const_mul (x^2*‖LSeries.term (fun m => (μ m : ℂ)) 2 n‖)).mono'
    hc.aestronglyMeasurable (Filter.Eventually.of_forall fun t => (t1_rieszLineTerm_norm k hx n t).le)

theorem t1_rieszLineTerm_integral {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (∫ t : ℝ, t1_rieszLineTerm k x n t) =
      (↑(2*Real.pi) : ℂ)*t1_moebiusKernelTerm k x n := by
  by_cases hn : n = 0
  · subst n
    simp [t1_rieszLineTerm,LSeries.term,t1_moebiusKernelTerm]
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hu : 0 < (n : ℝ)/x := div_pos hn0 hx
  have hpoint (t : ℝ) : t1_rieszLineTerm k x n t =
      (μ n : ℂ)*(((n : ℝ)/x : ℝ) : ℂ)^(-t1_verticalPoint 2 t)*
        (t1_rieszDenom k (t1_verticalPoint 2 t))⁻¹ := by
    let s := t1_verticalPoint 2 t
    have h := Complex.mul_cpow_ofReal_nonneg hu.le hx.le s
    rw [← Complex.ofReal_mul,div_mul_cancel₀ _ hx.ne',Complex.ofReal_natCast] at h
    change (x : ℂ)^s * LSeries.term (fun m => (μ m : ℂ)) s n * _ = _
    rw [LSeries.term_def,if_neg hn,h,Complex.cpow_neg]
    have hx0 : (x : ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    field_simp [hx0]
    rw [mul_comm (t1_rieszDenom k (t1_verticalPoint 2 t))]
  simp_rw [hpoint,mul_assoc,integral_const_mul,
    t1_rieszKernel_inversion hk (σ := 2) (by norm_num) hu,
    t1_moebiusKernelTerm,if_neg hn]
  ring

end Markov
