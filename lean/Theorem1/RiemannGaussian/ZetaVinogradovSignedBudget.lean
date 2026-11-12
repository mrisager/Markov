/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVinogradovLocalDisc
import RiemannGaussian.ZetaSignedPrimeSeries
import T1ZetaDiskDerivativeBounds
import T1ZetaPoleLogDerivative

/-! Actual two-height local bounds and the three-height prime inequality.
The pinned finite Blaschke product includes all analytic multiplicities. -/

namespace RiemannGaussian.ZetaVinogradovSignedBudget
noncomputable section
open Complex Metric Set Markov
open VinogradovNearOneBudget VinogradovScaleSelection ZetaVinogradovLocalDisc
open ZetaNearOneLocalDisc (center)

/-- The actual upper bound and the Euler-side reciprocal center cost. -/
def allowance (n : ℕ) (x t : ℝ) : ℝ :=
  profile n t + Real.log (2+1/x)

/-- The real pole-removed constant and the two complete disc bounds. -/
def budget (K : ℝ) (n : ℕ) (x t : ℝ) : ℝ :=
  3*K + (32*allowance n x t + 8*allowance n x (2*t))/delta n

private theorem translated_disc_bound (n : ℕ) (hn : 12 ≤ n) {x t : ℝ}
    (ht : (heightThreshold n : ℝ)+1 ≤ |t|) (hx : 0 < x) (hxu : x ≤ delta n/4) :
    ∀ z ∈ closedBall (0 : ℂ) (delta n/2),
      ‖t1_zetaDiscTranslate x t z‖ ≤ Real.exp (profile n t) := by
  intro z hz
  have hc : t1_verticalPoint (1+x) t = ZetaNearOneLocalDisc.center x t := by
    simp [t1_verticalPoint,ZetaNearOneLocalDisc.center,mul_comm]
  unfold t1_zetaDiscTranslate
  rw [hc]
  apply disc_norm_bound n hn ht hx hxu
  simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_right,sub_zero] using hz

/-- The actual signed source at a genuine zero is bounded by the two
Vinogradov disc costs and the actual real-axis pole estimate. -/
theorem source_le_budget {K : ℝ}
    (hK : ∀ x : ℝ, 0 < x → x ≤ 1 →
      (-logDeriv riemannZeta (((1+x : ℝ) : ℂ))).re ≤ 1/x+K)
    (n : ℕ) (hn : 12 ≤ n) (ρ : ℂ) (hρ : riemannZeta ρ = 0) {x : ℝ}
    (ht : (heightThreshold n : ℝ)+1 ≤ |ρ.im|)
    (hx : 0 < x) (hxu : x ≤ delta n/4) (hnear : x+1-ρ.re < delta n/4) :
    4*(1/(x+1-ρ.re) - 16*(x+1-ρ.re)/(delta n)^2) ≤ 3/x + budget K n x ρ.im := by
  have hn1 : 1 ≤ n := by omega
  have hδ := delta_pos n
  have hδu := delta_le n
  have hbT : (rootBase n : ℝ) ≤ heightThreshold n := by
    exact_mod_cast rootBase_le_heightThreshold hn1
  have hb : (16 : ℝ) ≤ rootBase n := by exact_mod_cast rootBase_ge_sixteen n
  have ht2 : (heightThreshold n : ℝ)+1 ≤ |2*ρ.im| := by
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith [abs_nonneg ρ.im]
  have hzero := t1_neg_logDeriv_zeta_disc_le_sub_zero
    (R := delta n/2) (B := profile n ρ.im) (by positivity) (by linarith)
    (profile_nonneg hn1 _) hx (by linarith) hρ (by linarith)
    (translated_disc_bound n hn ht hx hxu)
  have hdouble := t1_neg_logDeriv_zeta_disc_le
    (R := delta n/2) (B := profile n (2*ρ.im)) (by positivity) (by linarith)
    (profile_nonneg hn1 _) hx (by linarith) (translated_disc_bound n hn ht2 hx hxu)
  have hprime := neg_logDeriv_riemannZeta_three_height_nonneg
    (a := 1+x) (by linarith) ρ.im
  have hreal := hK x hx (by linarith)
  have hprime' : 0 ≤ 3*(-logDeriv riemannZeta (((1+x : ℝ) : ℂ))).re +
      4*(-logDeriv riemannZeta (t1_verticalPoint (1+x) ρ.im)).re +
      (-logDeriv riemannZeta (t1_verticalPoint (1+x) (2*ρ.im))).re := by
    simpa [t1_verticalPoint,mul_comm] using hprime
  have hcorr : 4*(x+1-ρ.re)/(delta n/2)^2 = 16*(x+1-ρ.re)/(delta n)^2 := by rw [div_pow,div_div_eq_mul_div]; ring
  rw [hcorr] at hzero
  unfold t1_zetaRadiusBudget at hzero hdouble
  unfold budget allowance
  have hR1 : 4*(profile n ρ.im + Real.log (2+1/x))/(delta n/2) =
      8*(profile n ρ.im + Real.log (2+1/x))/delta n := by rw [div_div_eq_mul_div]; ring
  have hR2 : 4*(profile n (2*ρ.im) + Real.log (2+1/x))/(delta n/2) =
      8*(profile n (2*ρ.im) + Real.log (2+1/x))/delta n := by rw [div_div_eq_mul_div]; ring
  rw [hR1] at hzero
  rw [hR2] at hdouble
  let U := profile n ρ.im + Real.log (2+1/x)
  let V := profile n (2*ρ.im) + Real.log (2+1/x)
  let Z := 1/(x+1-ρ.re) - 16*(x+1-ρ.re)/(delta n)^2
  change _ ≤ 8*U/delta n-Z at hzero
  change _ ≤ 8*V/delta n at hdouble
  change 4*Z ≤ 3/x+(3*K+(32*U+8*V)/delta n)
  have hsum := hprime'.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hreal (by norm_num : (0 : ℝ) ≤ 3))
    (mul_le_mul_of_nonneg_left hzero (by norm_num : (0 : ℝ) ≤ 4))) hdouble)
  have he : 3*(1/x+K)+4*(8*U/delta n-Z)+8*V/delta n =
      3/x+(3*K+(32*U+8*V)/delta n)-4*Z := by ring
  rw [he] at hsum
  exact sub_nonneg.mp hsum

/-- A paid actual two-height budget yields a strict zero exclusion. -/
theorem margin_of_budget {K : ℝ}
    (hK : ∀ x : ℝ, 0 < x → x ≤ 1 →
      (-logDeriv riemannZeta (((1+x : ℝ) : ℂ))).re ≤ 1/x+K)
    (n : ℕ) (hn : 12 ≤ n) (ρ : ℂ) (hρ : riemannZeta ρ = 0)
    (ht : (heightThreshold n : ℝ)+1 ≤ |ρ.im|) {d : ℝ} (hd : 0 < d)
    (hdsmall : d < delta n/28)
    (hpay : 14*d*budget K n (6*d) ρ.im + 6272*d^2/(delta n)^2 < 1) :
    d < 1-ρ.re := by
  by_contra! hgap
  have hρre : ρ.re < 1 := by
    by_contra! h
    exact riemannZeta_ne_zero_of_one_le_re h hρ
  let v := 6*d+1-ρ.re
  have hv : 0 < v := by dsimp [v]; linarith
  have hvup : v ≤ 7*d := by dsimp [v]; linarith
  have hsource := source_le_budget hK n hn ρ hρ ht (by positivity : 0 < 6*d)
    (by linarith : 6*d ≤ delta n/4) (by linarith : 6*d+1-ρ.re < delta n/4)
  change 4*(1/v - 16*v/(delta n)^2) ≤ 3/(6*d) + budget K n (6*d) ρ.im at hsource
  have hinv := one_div_le_one_div_of_le hv hvup
  have hcorr : 16*v/(delta n)^2 ≤ 112*d/(delta n)^2 :=
    div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
  have hs : 4*(1/(7*d)-112*d/(delta n)^2) ≤ 3/(6*d) + budget K n (6*d) ρ.im := by linarith
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 14*d)
  have hleft : 14*d*(4*(1/(7*d)-112*d/(delta n)^2)) =
      8-6272*d^2/(delta n)^2 := by field_simp; ring
  have hright : 14*d*(3/(6*d) + budget K n (6*d) ρ.im) =
      7+14*d*budget K n (6*d) ρ.im := by field_simp; ring
  rw [hleft,hright] at hm
  linarith

end
end RiemannGaussian.ZetaVinogradovSignedBudget

-- Modified from David Sanftenberg’s RiemannGaussian for the Lean 4.28.0 certificate.
