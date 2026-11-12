import T1ZetaFractionalFormula

/-! An actual polynomial growth bound for pole-removed zeta and a uniform
reciprocal bound on the line Re(s)=2. -/
noncomputable section
open Complex ArithmeticFunction
open scoped Moebius
namespace Markov

theorem t1_poleRemovedZeta_norm_le (s : ℂ) (hs : (1 : ℝ)/2 ≤ s.re) :
    ‖t1_poleRemovedZeta s‖ ≤ 3*(1+‖s‖)^2 := by
  have hsr : 0 < s.re := by linarith
  have hf : ‖t1_zetaFractionalMellin s‖ ≤ 2 := (t1_zetaFractionalMellin_norm_le hsr).trans
    ((div_le_iff₀ hsr).mpr (by linarith))
  have hsub : ‖s-1‖ ≤ ‖s‖+1 := by simpa only [norm_one] using norm_sub_le s 1
  rw [t1_poleRemovedZeta_fractional_formula hsr]
  calc
    _ ≤ ‖s‖+‖s*(s-1)*t1_zetaFractionalMellin s‖ := norm_sub_le _ _
    _ ≤ ‖s‖+‖s‖*(‖s‖+1)*2 := by
      simp only [norm_mul]
      exact add_le_add_right (mul_le_mul
        (mul_le_mul_of_nonneg_left hsub (norm_nonneg _)) hf (norm_nonneg _) (by positivity)) _
    _ ≤ _ := by nlinarith [norm_nonneg s]

theorem t1_reciprocalZeta_line_two_bounded :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, s.re = 2 → ‖t1_reciprocalZeta s‖ ≤ K := by
  let a := fun n => ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖
  have ha : Summable a := ((LSeriesSummable_one_iff.mpr (by norm_num : 1 < (2 : ℂ).re)) :
    Summable (LSeries.term (1 : ℕ → ℂ) (2 : ℂ))).norm
  have ha0 : 0 ≤ ∑' n, a n := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨(∑' n, a n)+1,by linarith,?_⟩
  intro s hs
  have hs' : 1 < s.re := by linarith
  have hm := (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs' :
    Summable (LSeries.term (fun n => (μ n : ℂ)) s)).norm
  have hterm (n : ℕ) : ‖LSeries.term (fun k => (μ k : ℂ)) s n‖ ≤ a n := by
    refine (LSeries.norm_term_le (g := (1 : ℕ → ℂ)) s ?_).trans ?_
    · rw [Complex.norm_intCast,← Int.cast_abs,Pi.one_apply,norm_one]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
    · simp only [a,LSeries.norm_term_eq,hs,show (2 : ℂ).re = 2 by norm_num,le_refl]
  rw [t1_reciprocalZeta_eq_moebius_LSeries hs',LSeries]
  exact (norm_tsum_le_tsum_norm hm).trans
    ((hm.tsum_le_tsum hterm ha).trans (le_add_of_nonneg_right zero_le_one))

theorem t1_poleRemovedZeta_reciprocal_line_two_bounded :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, s.re = 2 → ‖(t1_poleRemovedZeta s)⁻¹‖ ≤ K := by
  obtain ⟨K,hK,h⟩ := t1_reciprocalZeta_line_two_bounded
  refine ⟨K,hK,fun s hs => ?_⟩
  have hb := h s hs
  have hnorm : 1 ≤ ‖s-1‖ := by
    have hn := Complex.abs_re_le_norm (s-1)
    rwa [Complex.sub_re,hs,Complex.one_re,show (2 : ℝ)-1 = 1 by norm_num,abs_one] at hn
  rw [t1_reciprocalZeta,div_eq_mul_inv,norm_mul] at hb
  exact (le_mul_of_one_le_left (norm_nonneg _) hnorm).trans hb

end Markov
