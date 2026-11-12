import T1RieszLineTerm
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Exact vertical integral for the genuine smoothed Möbius sum on
Re(s)=2, with absolute termwise integration justified. -/
noncomputable section
open Complex MeasureTheory ArithmeticFunction
open scoped Moebius
namespace Markov

def t1_rieszIntegrand (k : ℕ) (x : ℝ) (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  (x : ℂ)^s*F s*(t1_rieszDenom k s)⁻¹

theorem t1_rieszLineTerm_summable_integral_norm {k : ℕ} {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖t1_rieszLineTerm k x n t‖) := by
  have hS := (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr
    (show 1 < (2 : ℂ).re by norm_num) :
      Summable (LSeries.term (fun m => (μ m : ℂ)) 2)).norm
  simp_rw [t1_rieszLineTerm_norm k hx,integral_const_mul]
  exact (hS.mul_left (x^2)).mul_right _

theorem t1_rieszLineTerm_tsum (k : ℕ) (x t : ℝ) :
    (∑' n, t1_rieszLineTerm k x n t) =
      t1_rieszIntegrand k x t1_reciprocalZeta (t1_verticalPoint 2 t) := by
  have hs : 1 < (t1_verticalPoint 2 t).re := by rw [t1_verticalPoint_re]; norm_num
  simp only [t1_rieszLineTerm,tsum_mul_right,tsum_mul_left,t1_rieszIntegrand]
  rw [← LSeries,← t1_reciprocalZeta_eq_moebius_LSeries hs]

theorem t1_rieszMertens_integral_line_two {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : 0 < x) :
    (t1_rieszMertens k x : ℂ) = (x : ℂ)^k/(↑(2*Real.pi) : ℂ) *
      ∫ t : ℝ, t1_rieszIntegrand k x t1_reciprocalZeta (t1_verticalPoint 2 t) := by
  have h := integral_tsum_of_summable_integral_norm (t1_rieszLineTerm_integrable hk hx)
    (t1_rieszLineTerm_summable_integral_norm (k := k) hx)
  simp_rw [t1_rieszLineTerm_integral hk hx,t1_rieszLineTerm_tsum,tsum_mul_left] at h
  rw [t1_rieszMertens_eq_tsum hk hx,← h]
  have hp : (↑(2*Real.pi) : ℂ) ≠ 0 := by exact_mod_cast (show 2*Real.pi ≠ 0 by positivity)
  field_simp [hp]

end Markov
