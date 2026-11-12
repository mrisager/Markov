import T1RieszMellinKernel
import T1VerticalPower

/-! Nonvanishing and uniform vertical decay of the explicit Riesz kernel
denominator, for all real parts at least one half. -/
noncomputable section
open Complex MeasureTheory Set
namespace Markov

theorem t1_rieszDenom_ne_zero (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    t1_rieszDenom k s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  have h : 0 < (s+(j : ℂ)).re := by
    simp only [Complex.add_re,Complex.natCast_re]
    positivity
  intro hz
  rw [hz,Complex.zero_re] at h
  exact (lt_irrefl (0 : ℝ)) h

theorem t1_rieszDenom_differentiable (k : ℕ) : Differentiable ℂ (t1_rieszDenom k) := by
  unfold t1_rieszDenom
  fun_prop

theorem t1_rieszDenom_inv_norm_le (k : ℕ) {s : ℂ} (hs : (1 : ℝ)/2 ≤ s.re) :
    ‖(t1_rieszDenom k s)⁻¹‖ ≤ (3 : ℝ)^(k+1)*(1+|s.im|)^(-((k : ℝ)+1)) := by
  let u := 1+|s.im|
  have hu : 0 < u := by dsimp [u]; positivity
  have hfactor (j : ℕ) : ‖(s+(j : ℂ))⁻¹‖ ≤ 3/u := by
    have hre : (1 : ℝ)/2 ≤ (s+(j : ℂ)).re := by
      simp only [Complex.add_re,Complex.natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) j]
    have him : |s.im| ≤ ‖s+(j : ℂ)‖ := by
      simpa only [Complex.add_im,Complex.natCast_im,add_zero] using
        Complex.abs_im_le_norm (s+(j : ℂ))
    have hn := (le_abs_self (s+(j : ℂ)).re).trans (Complex.abs_re_le_norm _)
    have hn0 : 0 < ‖s+(j : ℂ)‖ := by linarith
    rw [norm_inv,← one_div]
    apply (div_le_div_iff₀ hn0 hu).mpr
    dsimp [u]
    linarith
  calc
    _ = ∏ j ∈ Finset.range (k+1), ‖(s+(j : ℂ))⁻¹‖ := by
      rw [t1_rieszDenom,← Finset.prod_inv_distrib,norm_prod]
    _ ≤ ∏ _j ∈ Finset.range (k+1), 3/u :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hfactor j)
    _ = _ := by
      rw [Finset.prod_const,Finset.card_range,div_pow]
      change (3 : ℝ)^(k+1)/u^(k+1) = (3 : ℝ)^(k+1)*u^(-((k : ℝ)+1))
      rw [Real.rpow_neg hu.le,← Nat.cast_succ,Real.rpow_natCast,div_eq_mul_inv]

theorem t1_rieszDenom_inv_verticalIntegrable {k : ℕ} (hk : 0 < k) {σ : ℝ}
    (hσ : (1 : ℝ)/2 ≤ σ) :
    VerticalIntegrable (fun s => (t1_rieszDenom k s)⁻¹) σ := by
  have hneg : -((k : ℝ)+1) < -1 := by
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    linarith
  have hi := (t1_verticalPower_integrable (-((k : ℝ)+1)) hneg).const_mul ((3 : ℝ)^(k+1))
  have hRe (t : ℝ) : (((σ : ℂ)+(t : ℂ)*I) : ℂ).re = σ := by simp
  have hIm (t : ℝ) : (((σ : ℂ)+(t : ℂ)*I) : ℂ).im = t := by simp
  have hcont : Continuous (fun t : ℝ => (t1_rieszDenom k ((σ : ℂ)+(t : ℂ)*I))⁻¹) := by
    apply Continuous.inv₀
    · exact (t1_rieszDenom_differentiable k).continuous.comp (by fun_prop)
    · intro t
      apply t1_rieszDenom_ne_zero
      rw [hRe]
      linarith
  refine hi.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with t
  simpa only [hIm] using t1_rieszDenom_inv_norm_le k (s := (σ : ℂ)+(t : ℂ)*I)
    (by rwa [hRe])

end Markov
