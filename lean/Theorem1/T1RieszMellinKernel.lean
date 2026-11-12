import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! The Mellin transform of the positive-part polynomial Riesz kernel.
The denominator is the actual product of k+1 linear factors. -/
noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Nat
namespace Markov

def t1_rieszKernel (k : ℕ) (u : ℝ) : ℂ := ((max (1-u) 0 : ℝ) : ℂ)^k/(k ! : ℂ)

def t1_rieszDenom (k : ℕ) (s : ℂ) : ℂ := ∏ j ∈ Finset.range (k+1), (s+(j : ℂ))

theorem t1_rieszKernel_continuous (k : ℕ) : Continuous (t1_rieszKernel k) := by
  unfold t1_rieszKernel
  fun_prop

theorem t1_rieszKernel_hasMellin {k : ℕ} (hk : 0 < k) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (t1_rieszKernel k) s (1/t1_rieszDenom k s) := by
  let F := fun u : ℝ => (u : ℂ)^(s-1)*(1-(u : ℂ))^k/(k ! : ℂ)
  have hpoint (u : ℝ) (hu : u ∈ Ioi (0 : ℝ)) :
      (u : ℂ)^(s-1) • t1_rieszKernel k u = (Ioc (0 : ℝ) 1).indicator F u := by
    by_cases h : u ≤ 1
    · rw [indicator_of_mem (show u ∈ Ioc (0 : ℝ) 1 from ⟨hu,h⟩)]
      dsimp only [F]
      rw [t1_rieszKernel,max_eq_left (sub_nonneg.mpr h),smul_eq_mul,
        Complex.ofReal_sub,Complex.ofReal_one,mul_div_assoc]
    · rw [indicator_of_notMem (show u ∉ Ioc (0 : ℝ) 1 from fun h' => h h'.2),
        t1_rieszKernel,max_eq_right (sub_nonpos.mpr (le_of_not_ge h)),Complex.ofReal_zero,
        zero_pow hk.ne',zero_div,smul_zero]
  have hAE : (fun u : ℝ => (u : ℂ)^(s-1) • t1_rieszKernel k u) =ᵐ[volume.restrict (Ioi 0)]
      (Ioc (0 : ℝ) 1).indicator F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu using hpoint u hu
  have harg : 0 < ((k : ℂ)+1).re := by simp only [add_re,natCast_re,one_re]; positivity
  have hint : IntervalIntegrable F volume 0 1 := by
    have h := (betaIntegral_convergent hs harg).div_const (k ! : ℂ)
    simpa only [add_sub_cancel_right,Complex.cpow_natCast,F] using h
  refine ⟨?_,?_⟩
  · rw [MellinConvergent,IntegrableOn,integrable_congr hAE,
      integrable_indicator_iff measurableSet_Ioc,IntegrableOn,
      Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hint
  · rw [mellin,integral_congr_ae hAE,integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self,
      ← intervalIntegral.integral_of_le (show (0 : ℝ)≤1 by norm_num)]
    have hEq : (∫ u : ℝ in (0 : ℝ)..1, F u) = betaIntegral s ((k : ℂ)+1)/(k ! : ℂ) := by
      rw [betaIntegral]
      simp only [add_sub_cancel_right,Complex.cpow_natCast,F,intervalIntegral.integral_div]
    rw [hEq,betaIntegral_eval_nat_add_one_right hs,t1_rieszDenom]
    have hk0 : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp [hk0]

end Markov
