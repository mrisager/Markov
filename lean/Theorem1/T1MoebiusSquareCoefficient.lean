import T1MertensFinite
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-! The exact Möbius square-series coefficient from mathlib's proved
Dirichlet-series inverse identity and Euler's zeta(2) evaluation. -/
noncomputable section
open Classical
open scoped ArithmeticFunction.Moebius
namespace Markov

def t1_moebiusSquareTerm (n : ℕ) : ℝ := (μ n : ℝ) / (n : ℝ)^2

theorem t1_moebiusSquareTerm_complex (n : ℕ) :
    (t1_moebiusSquareTerm n : ℂ) =
      LSeries.term (fun n => (μ n : ℂ)) 2 n := by
  by_cases hn : n = 0
  · simp [hn, t1_moebiusSquareTerm]
  · rw [LSeries.term_of_ne_zero hn]
    simp [t1_moebiusSquareTerm, Complex.cpow_ofNat]

theorem t1_moebiusSquareTerm_summable : Summable t1_moebiusSquareTerm := by
  have h : LSeriesSummable (fun n => (μ n : ℂ)) 2 :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by norm_num)
  apply Complex.summable_ofReal.mp
  exact h.congr (fun n => (t1_moebiusSquareTerm_complex n).symm)

theorem t1_moebiusSquareTerm_tsum :
    ∑' n, t1_moebiusSquareTerm n = 6 / Real.pi^2 := by
  have hc : ((∑' n, t1_moebiusSquareTerm n : ℝ) : ℂ) =
      LSeries (fun n => (μ n : ℂ)) 2 := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr t1_moebiusSquareTerm_complex
  have hinv := LSeries_one_mul_Lseries_moebius (s := (2 : ℂ)) (by norm_num)
  rw [LSeries_one_eq_riemannZeta (by norm_num), riemannZeta_two, ← hc] at hinv
  have hr : Real.pi^2 / 6 * (∑' n, t1_moebiusSquareTerm n) = 1 := by
    exact_mod_cast hinv
  have hp : Real.pi^2 ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  apply (eq_div_iff hp).mpr
  nlinarith

end Markov
