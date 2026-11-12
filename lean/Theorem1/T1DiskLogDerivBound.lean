/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Sharp center derivative control from a one-sided real-part bound

The Schwarz transform `f / (2*M-f)` retains the complete complex derivative.
Applying Schwarz directly at the center gives the classical Carathéodory
constant `2`, without first taking a maximum on a smaller auxiliary circle.
The radius is arbitrary, including radii shrinking along another parameter.
-/

namespace Markov
noncomputable section
open Complex Metric Set

/-- A normalized holomorphic function with real part at most `M` on a
disc has center derivative bounded by `2*M/R`. The hypothesis is one-sided;
no bound on the imaginary part or the function's norm is required. -/
theorem t1_caratheodory_norm_deriv_zero_le {f : ℂ → ℂ} {M R : ℝ} (hM : 0 < M) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hreal : ∀ z ∈ ball 0 R, (f z).re ≤ M)
    (hzero : f 0 = 0) : ‖deriv f 0‖ ≤ 2 * M / R := by
  let w : ℂ → ℂ := fun z ↦ f z / (2 * (M : ℂ) - f z)
  have hden : ∀ z ∈ ball (0 : ℂ) R, 2 * (M : ℂ) - f z ≠ 0 := by
    intro z hz he
    have hr := hreal z hz
    have he' := congrArg Complex.re (sub_eq_zero.mp he)
    norm_num at he'
    linarith
  have hw : DifferentiableOn ℂ w (ball 0 R) :=
    hf.div (hf.const_sub _) hden
  have hwzero : w 0 = 0 := by simp [w, hzero]
  have hmaps : MapsTo w (ball 0 R) (closedBall (w 0) 1) := by
    intro z hz
    rw [hwzero, mem_closedBall, dist_zero_right]
    change ‖f z / (2 * (M : ℂ) - f z)‖ ≤ 1
    rw [norm_div]
    apply div_le_one_of_le₀ _ (norm_nonneg _)
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    have hr := hreal z hz
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im]
    norm_num
    nlinarith
  have hs := Complex.norm_deriv_le_div_of_mapsTo_ball hw hmaps hR
  have hf0 := (hf 0 (mem_ball_self hR)).differentiableAt (isOpen_ball.mem_nhds
    (mem_ball_self hR))
  have hd := hf0.hasDerivAt.div (hf0.hasDerivAt.const_sub (2 * (M : ℂ)))
    (hden 0 (mem_ball_self hR))
  have hwd : deriv w 0 = deriv f 0 / (2 * (M : ℂ)) := by
    change deriv (f / fun z ↦ 2 * (M : ℂ) - f z) 0 = _
    rw [hd.deriv]
    simp only [hzero, sub_zero, zero_mul, sub_zero]
    field_simp
  rw [hwd, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hM] at hs
  have h := (div_le_iff₀ (by positivity : 0 < 2 * M)).mp hs
  exact h.trans_eq (by ring)


variable {g L : ℂ → ℂ} {R : ℝ}

/-- A zero-free analytic disc has a logarithmic primitive normalized
at its center. -/
private theorem exists_logarithm (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hne : ∀ z ∈ closedBall 0 R, g z ≠ 0) :
    ∃ L : ℂ → ℂ, L 0 = 0 ∧ ∀ z ∈ ball 0 R, HasDerivAt L (logDeriv g z) z := by
  have hd : DifferentiableOn ℂ (logDeriv g) (ball 0 R) := by
    intro z hz
    have ha := hg z (ball_subset_closedBall hz)
    have hl : AnalyticAt ℂ (logDeriv g) z := by
      simpa only [logDeriv] using ha.deriv.div ha (hne z (ball_subset_closedBall hz))
    exact hl.differentiableAt.differentiableWithinAt
  obtain ⟨p,hp⟩ := hd.isExactOn_ball
  exact ⟨fun z => p z-p 0,sub_self _,fun z hz => (hp z hz).sub_const _⟩

/-- The normalized primitive exponentiates to the full original
function divided by its actual nonzero center value. -/
private theorem exp_mul_center (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hne : ∀ z ∈ closedBall 0 R, g z ≠ 0) (hL0 : L 0 = 0)
    (hL : ∀ z ∈ ball 0 R, HasDerivAt L (logDeriv g z) z)
    {z : ℂ} (hz : z ∈ ball 0 R) : Complex.exp (L z) * g 0 = g z := by
  let q : ℂ → ℂ := (fun w ↦ Complex.exp (-L w)) * g
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hdiff : DifferentiableOn ℂ q (ball 0 R) := by
    intro w hw
    exact ((hL w hw).neg.cexp.mul
      (hg w (ball_subset_closedBall hw)).differentiableAt.hasDerivAt).differentiableAt.differentiableWithinAt
  have hderiv : EqOn (deriv q) 0 (ball 0 R) := by
    intro w hw
    have hq : HasDerivAt q
        (Complex.exp (-L w) * (-logDeriv g w) * g w + Complex.exp (-L w) * deriv g w) w :=
      (hL w hw).neg.cexp.mul (hg w (ball_subset_closedBall hw)).differentiableAt.hasDerivAt
    rw [hq.deriv]
    change Complex.exp (-L w) * (-logDeriv g w) * g w +
      Complex.exp (-L w) * deriv g w = 0
    rw [logDeriv_apply, mul_assoc (Complex.exp (-L w)) (-(deriv g w / g w)) (g w),
      neg_mul, div_mul_cancel₀ _ (hne w (ball_subset_closedBall hw))]
    ring
  have he := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) R).isPreconnected
    hdiff hderiv hzero hz
  have hg0 : g 0 = Complex.exp (-L z) * g z := by simpa [q, hL0] using he
  rw [hg0, ← mul_assoc, ← Complex.exp_add]
  simp

/-- The real part of the normalized logarithm pays exactly the growth
allowance and the center's negative logarithm. -/
private theorem realPart_le (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hne : ∀ z ∈ closedBall 0 R, g z ≠ 0) (hL0 : L 0 = 0)
    (hL : ∀ z ∈ ball 0 R, HasDerivAt L (logDeriv g z) z)
    {B C : ℝ} (hB : ∀ z ∈ closedBall 0 R, ‖g z‖ ≤ Real.exp B)
    (hC : -Real.log ‖g 0‖ ≤ C) {z : ℂ} (hz : z ∈ ball 0 R) :
    (L z).re ≤ B + C := by
  have hp0 : 0 < ‖g 0‖ := norm_pos_iff.mpr (hne 0 (mem_closedBall_self hR.le))
  have hpz : 0 < ‖g z‖ := norm_pos_iff.mpr (hne z (ball_subset_closedBall hz))
  have he := congrArg norm (exp_mul_center hR hg hne hL0 hL hz)
  rw [norm_mul, Complex.norm_exp] at he
  have hl := congrArg Real.log he
  rw [Real.log_mul (Real.exp_pos _).ne' hp0.ne', Real.log_exp] at hl
  have hb := Real.log_le_log hpz (hB z (ball_subset_closedBall hz))
  rw [Real.log_exp] at hb
  linarith

/-- The sharp Carathéodory estimate controls the complete logarithmic
derivative at the center with constant two, retaining the actual center
allowance and every positive disc radius. -/
theorem t1_disk_norm_logDeriv_center_le (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hne : ∀ z ∈ closedBall 0 R, g z ≠ 0)
    {B C : ℝ} (hA : 0 < B + C)
    (hB : ∀ z ∈ closedBall 0 R, ‖g z‖ ≤ Real.exp B)
    (hC : -Real.log ‖g 0‖ ≤ C) : ‖logDeriv g 0‖ ≤ 2 * (B + C) / R := by
  obtain ⟨L, hL0, hL⟩ := exists_logarithm hg hne
  have hd0 := t1_caratheodory_norm_deriv_zero_le hA hR
    (fun z hz ↦ (hL z hz).differentiableAt.differentiableWithinAt)
    (fun z hz ↦ realPart_le hR hg hne hL0 hL hB hC hz) hL0
  rw [(hL 0 (mem_ball_self hR)).deriv] at hd0
  exact hd0

end
end Markov
