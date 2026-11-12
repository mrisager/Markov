import T1ZetaGrowth

/-! A bound for reciprocal zeta just to the right of the pole line,
uniform in the imaginary coordinate. -/
noncomputable section
open Complex ArithmeticFunction
open scoped Moebius
namespace Markov

theorem t1_LSeries_one_real_term_eq_norm (σ : ℝ) (n : ℕ) :
    LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n =
      (↑‖LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n‖ : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  simp only [LSeries.term_def,if_neg hn,Pi.one_apply]
  rw [← Complex.ofReal_natCast,← Complex.ofReal_cpow (by positivity : 0 ≤ (n : ℝ)),
    ← Complex.ofReal_one,← Complex.ofReal_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

theorem t1_reciprocalZeta_norm_le_real_zeta {s : ℂ} (hs : 1 < s.re) :
    ‖t1_reciprocalZeta s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ := by
  let σ := s.re
  let a := fun n => ‖LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n‖
  have hσ : 1 < (σ : ℂ).re := by simpa only [Complex.ofReal_re] using hs
  have ha : Summable a := ((LSeriesSummable_one_iff.mpr hσ) :
    Summable (LSeries.term (1 : ℕ → ℂ) (σ : ℂ))).norm
  have hm := (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs :
    Summable (LSeries.term (fun n => (μ n : ℂ)) s)).norm
  have hterm (n : ℕ) : ‖LSeries.term (fun k => (μ k : ℂ)) s n‖ ≤ a n := by
    refine (LSeries.norm_term_le (g := (1 : ℕ → ℂ)) s ?_).trans ?_
    · rw [Complex.norm_intCast,← Int.cast_abs,Pi.one_apply,norm_one]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    · simp only [a,LSeries.norm_term_eq,Complex.ofReal_re,σ,le_refl]
  have hζ : riemannZeta (σ : ℂ) = (↑(∑' n, a n) : ℂ) := by
    rw [← LSeries_one_eq_riemannZeta hσ,LSeries,Complex.ofReal_tsum]
    exact tsum_congr (t1_LSeries_one_real_term_eq_norm σ)
  have ha0 : 0 ≤ ∑' n, a n := tsum_nonneg (fun _ => norm_nonneg _)
  rw [t1_reciprocalZeta_eq_moebius_LSeries hs,LSeries,hζ,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ha0]
  exact (norm_tsum_le_tsum_norm hm).trans (hm.tsum_le_tsum hterm ha)

theorem t1_reciprocalZeta_norm_le_right {s : ℂ} (hs : 1 < s.re) :
    ‖t1_reciprocalZeta s‖ ≤ 2+1/(s.re-1) := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : 0 < s.re-1 := sub_pos.mpr hs
  have hζ := t1_zeta_fractional_formula_right (s := (s.re : ℂ)) (by simpa only [Complex.ofReal_re])
  have hb := t1_zetaFractionalMellin_norm_le (s := (s.re : ℂ)) (by simpa only [Complex.ofReal_re])
  rw [Complex.ofReal_re] at hb
  apply (t1_reciprocalZeta_norm_le_real_zeta hs).trans
  rw [hζ]
  calc
    _ ≤ ‖(s.re : ℂ)/((s.re : ℂ)-1)‖ + ‖(s.re : ℂ)*t1_zetaFractionalMellin (s.re : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ s.re/(s.re-1)+s.re*(1/s.re) := by
      rw [norm_div,norm_mul,← Complex.ofReal_one,← Complex.ofReal_sub,
        Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hs0,
        abs_of_pos hs1]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hb hs0.le) _
    _ = _ := by field_simp [hs0.ne',hs1.ne']; ring

end Markov
