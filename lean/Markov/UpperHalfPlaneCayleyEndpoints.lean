import Markov.UpperHalfPlaneCayley

noncomputable section
open Filter Topology
namespace Markov

theorem hyperbolicVerticalAxis_complex_norm (x : ℝ) :
    ‖(hyperbolicVerticalAxis x : ℂ)‖ = Real.exp x := by
  change ‖(⟨0, Real.exp x⟩ : ℂ)‖ = Real.exp x
  rw [Complex.norm_def]
  change Real.sqrt (0*0 + Real.exp x * Real.exp x) = Real.exp x
  rw [zero_mul, zero_add]
  exact Real.sqrt_mul_self (Real.exp_pos x).le

/-- A hyperbolic distance bound to the literal vertical point bounds the actual
complex norm, with the scale of that vertical point retained. -/
theorem upperHalfPlane_complex_norm_le_of_dist_vertical
    (z : UpperHalfPlane) (x B : ℝ)
    (h : dist z (hyperbolicVerticalAxis x) ≤ B) :
    ‖(z : ℂ)‖ ≤ Real.exp x * Real.exp B := by
  have hd := UpperHalfPlane.dist_coe_le z (hyperbolicVerticalAxis x)
  change dist (z : ℂ) (hyperbolicVerticalAxis x : ℂ) ≤
    Real.exp x * (Real.exp (dist z (hyperbolicVerticalAxis x)) - 1) at hd
  calc
    ‖(z : ℂ)‖ ≤ dist (z : ℂ) (hyperbolicVerticalAxis x : ℂ) +
        ‖(hyperbolicVerticalAxis x : ℂ)‖ := by
      simpa only [dist_zero_right] using
        dist_triangle (z : ℂ) (hyperbolicVerticalAxis x : ℂ) (0 : ℂ)
    _ ≤ Real.exp x * (Real.exp (dist z (hyperbolicVerticalAxis x)) - 1) +
        Real.exp x := by rw [hyperbolicVerticalAxis_complex_norm]; linarith
    _ = Real.exp x * Real.exp (dist z (hyperbolicVerticalAxis x)) := by ring
    _ ≤ Real.exp x * Real.exp B :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h) (Real.exp_pos x).le

theorem upperHalfPlane_im_lower_of_dist_vertical
    (z : UpperHalfPlane) (x B : ℝ)
    (h : dist z (hyperbolicVerticalAxis x) ≤ B) :
    Real.exp x / Real.exp B ≤ z.im := by
  have hd := UpperHalfPlane.im_div_exp_dist_le (hyperbolicVerticalAxis x) z
  change Real.exp x / Real.exp (dist (hyperbolicVerticalAxis x) z) ≤ z.im at hd
  calc
    Real.exp x / Real.exp B ≤
        Real.exp x / Real.exp (dist (hyperbolicVerticalAxis x) z) := by
      apply div_le_div_of_nonneg_left (Real.exp_pos x).le (Real.exp_pos _)
      exact Real.exp_le_exp.mpr (by simpa only [dist_comm] using h)
    _ ≤ z.im := hd

theorem upperHalfPlaneCayley_norm_add_one_le_of_dist_vertical
    (z : UpperHalfPlane) (x B : ℝ)
    (h : dist z (hyperbolicVerticalAxis x) ≤ B) :
    ‖upperHalfPlaneCayley z + 1‖ ≤ 2 * Real.exp x * Real.exp B := by
  calc
    ‖upperHalfPlaneCayley z + 1‖ ≤ 2 * ‖(z : ℂ)‖ :=
      upperHalfPlaneCayley_norm_add_one_le z
    _ ≤ 2 * (Real.exp x * Real.exp B) := by
      gcongr
      exact upperHalfPlane_complex_norm_le_of_dist_vertical z x B h
    _ = 2 * Real.exp x * Real.exp B := by ring

theorem upperHalfPlaneCayley_norm_sub_one_le_of_dist_vertical
    (z : UpperHalfPlane) (x B : ℝ)
    (h : dist z (hyperbolicVerticalAxis x) ≤ B) :
    ‖upperHalfPlaneCayley z - 1‖ ≤ (2 * Real.exp B) * Real.exp (-x) := by
  calc
    ‖upperHalfPlaneCayley z - 1‖ ≤ 2 / (z.im + 1) :=
      upperHalfPlaneCayley_norm_sub_one_le z
    _ ≤ 2 / (Real.exp x / Real.exp B) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have hl := upperHalfPlane_im_lower_of_dist_vertical z x B h
      linarith
    _ = (2 * Real.exp B) * Real.exp (-x) := by
      rw [Real.exp_neg]
      field_simp

/-- Any curve uniformly close to a positive-speed actual vertical line has
the negative Cayley endpoint -1. No continuity of the curve is needed. -/
theorem upperHalfPlaneCayley_tendsto_atBot_of_dist_vertical
    (γ : ℝ → UpperHalfPlane) (k B : ℝ) (hk : 0 < k)
    (h : ∀ t, dist (γ t) (hyperbolicVerticalAxis (k*t)) ≤ B) :
    Tendsto (fun t => upperHalfPlaneCayley (γ t)) atBot (𝓝 (-1 : ℂ)) := by
  have hkt : Tendsto (fun t : ℝ => k*t) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos hk).mpr tendsto_id
  have he : Tendsto (fun t : ℝ => 2 * Real.exp (k*t) * Real.exp B)
      atBot (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((Real.tendsto_exp_atBot.comp hkt).const_mul 2).mul_const (Real.exp B)
  have hz : Tendsto (fun t => upperHalfPlaneCayley (γ t) + 1) atBot (𝓝 (0 : ℂ)) :=
    squeeze_zero_norm (fun t =>
      upperHalfPlaneCayley_norm_add_one_le_of_dist_vertical (γ t) (k*t) B (h t)) he
  simpa only [zero_sub, add_sub_cancel_right] using hz.sub_const (1 : ℂ)

/-- Any curve uniformly close to a positive-speed actual vertical line has
the positive Cayley endpoint +1. No continuity of the curve is needed. -/
theorem upperHalfPlaneCayley_tendsto_atTop_of_dist_vertical
    (γ : ℝ → UpperHalfPlane) (k B : ℝ) (hk : 0 < k)
    (h : ∀ t, dist (γ t) (hyperbolicVerticalAxis (k*t)) ≤ B) :
    Tendsto (fun t => upperHalfPlaneCayley (γ t)) atTop (𝓝 (1 : ℂ)) := by
  have hkt : Tendsto (fun t : ℝ => k*t) atTop atTop :=
    tendsto_id.const_mul_atTop hk
  have he : Tendsto (fun t : ℝ => (2 * Real.exp B) * Real.exp (-(k*t)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hkt).const_mul (2 * Real.exp B)
  have hz : Tendsto (fun t => upperHalfPlaneCayley (γ t) - 1) atTop (𝓝 (0 : ℂ)) :=
    squeeze_zero_norm (fun t =>
      upperHalfPlaneCayley_norm_sub_one_le_of_dist_vertical (γ t) (k*t) B (h t)) he
  simpa only [zero_add, sub_add_cancel] using hz.add_const (1 : ℂ)

end Markov
