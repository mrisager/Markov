import Markov.UpperHalfPlaneCayleyEndpoints
import Mathlib.Analysis.Normed.Field.Lemmas

/-! Literal SL/Cayley rational formulas and the two actual ideal column
endpoints. No abstract boundary action or compactification is assumed. -/

noncomputable section
open Filter Topology
open scoped MatrixGroups
namespace Markov

/-- The actual column endpoint corresponding to the original point zero. -/
def upperHalfPlaneCayleySLZero (h : SL(2, ℝ)) : ℂ :=
  ((h 0 1 : ℂ) - Complex.I * (h 1 1 : ℂ)) /
    ((h 0 1 : ℂ) + Complex.I * (h 1 1 : ℂ))

/-- The actual column endpoint corresponding to the original point infinity. -/
def upperHalfPlaneCayleySLInfinity (h : SL(2, ℝ)) : ℂ :=
  ((h 0 0 : ℂ) - Complex.I * (h 1 0 : ℂ)) /
    ((h 0 0 : ℂ) + Complex.I * (h 1 0 : ℂ))

private theorem cayleySL_det (h : SL(2, ℝ)) :
    h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using h.det_coe

theorem upperHalfPlaneCayleySLZero_den_ne_zero (h : SL(2, ℝ)) :
    (h 0 1 : ℂ) + Complex.I * (h 1 1 : ℂ) ≠ 0 := by
  intro he
  have hb : h 0 1 = 0 := by simpa using congrArg Complex.re he
  have hd : h 1 1 = 0 := by simpa using congrArg Complex.im he
  have hdet := cayleySL_det h
  rw [hb, hd] at hdet
  norm_num at hdet

theorem upperHalfPlaneCayleySLInfinity_den_ne_zero (h : SL(2, ℝ)) :
    (h 0 0 : ℂ) + Complex.I * (h 1 0 : ℂ) ≠ 0 := by
  intro he
  have ha : h 0 0 = 0 := by simpa using congrArg Complex.re he
  have hc : h 1 0 = 0 := by simpa using congrArg Complex.im he
  have hdet := cayleySL_det h
  rw [ha, hc] at hdet
  norm_num at hdet

private theorem cayleySL_column_norm (x y : ℝ)
    (hden : (x : ℂ) + Complex.I * (y : ℂ) ≠ 0) :
    ‖((x : ℂ) - Complex.I * (y : ℂ)) / ((x : ℂ) + Complex.I * (y : ℂ))‖ = 1 := by
  have hc : (x : ℂ) - Complex.I * (y : ℂ) =
      star ((x : ℂ) + Complex.I * (y : ℂ)) := by
    simp [sub_eq_add_neg]
  rw [hc, norm_div, norm_star, div_self (norm_ne_zero_iff.mpr hden)]

theorem upperHalfPlaneCayleySLZero_norm (h : SL(2, ℝ)) :
    ‖upperHalfPlaneCayleySLZero h‖ = 1 :=
  cayleySL_column_norm _ _ (upperHalfPlaneCayleySLZero_den_ne_zero h)

theorem upperHalfPlaneCayleySLInfinity_norm (h : SL(2, ℝ)) :
    ‖upperHalfPlaneCayleySLInfinity h‖ = 1 :=
  cayleySL_column_norm _ _ (upperHalfPlaneCayleySLInfinity_den_ne_zero h)

theorem upperHalfPlaneCayleySLZero_ne_infinity (h : SL(2, ℝ)) :
    upperHalfPlaneCayleySLZero h ≠ upperHalfPlaneCayleySLInfinity h := by
  intro he
  have hcross := (div_eq_div_iff (upperHalfPlaneCayleySLZero_den_ne_zero h)
    (upperHalfPlaneCayleySLInfinity_den_ne_zero h)).mp he
  have hi := congrArg Complex.im hcross
  simp [Complex.mul_im] at hi
  have hdet := cayleySL_det h
  nlinarith

private theorem cayleySL_action_den_ne_zero (h : SL(2, ℝ)) (z : UpperHalfPlane) :
    (h 1 0 : ℂ) * (z : ℂ) + (h 1 1 : ℂ) ≠ 0 := by
  intro he
  have hi : h 1 0 * z.im = 0 := by
    simpa [Complex.mul_im] using congrArg Complex.im he
  have hc : h 1 0 = 0 := (mul_eq_zero.mp hi).resolve_right z.im_ne_zero
  have hd : h 1 1 = 0 := by simpa [hc] using congrArg Complex.re he
  have hdet := cayleySL_det h
  rw [hc, hd] at hdet
  norm_num at hdet

private theorem cayleySL_action_formula (h : SL(2, ℝ)) (z : UpperHalfPlane) :
    ((h • z : UpperHalfPlane) : ℂ) =
      ((h 0 0 : ℂ) * (z : ℂ) + (h 0 1 : ℂ)) /
        ((h 1 0 : ℂ) * (z : ℂ) + (h 1 1 : ℂ)) := by
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
    UpperHalfPlane.coe_specialLinearGroup_apply h z

theorem upperHalfPlaneCayley_smul_den_ne_zero (h : SL(2, ℝ)) (z : UpperHalfPlane) :
    ((h 0 0 : ℂ) + Complex.I * (h 1 0 : ℂ)) * (z : ℂ) +
      ((h 0 1 : ℂ) + Complex.I * (h 1 1 : ℂ)) ≠ 0 := by
  have hd := cayleySL_action_den_ne_zero h z
  have hc := upperHalfPlaneCayley_den_ne_zero (h • z)
  rw [cayleySL_action_formula] at hc
  have hf :
      ((h 0 0 : ℂ) + Complex.I * (h 1 0 : ℂ)) * (z : ℂ) +
        ((h 0 1 : ℂ) + Complex.I * (h 1 1 : ℂ)) =
      ((((h 0 0 : ℂ) * (z : ℂ) + (h 0 1 : ℂ)) /
        ((h 1 0 : ℂ) * (z : ℂ) + (h 1 1 : ℂ))) + Complex.I) *
        ((h 1 0 : ℂ) * (z : ℂ) + (h 1 1 : ℂ)) := by
    field_simp [hd]
    ring
  rw [hf]
  exact mul_ne_zero hc hd

/-- The literal rational formula for the actual SL action followed by Cayley. -/
theorem upperHalfPlaneCayley_smul (h : SL(2, ℝ)) (z : UpperHalfPlane) :
    upperHalfPlaneCayley (h • z) =
      (((h 0 0 : ℂ) - Complex.I * (h 1 0 : ℂ)) * (z : ℂ) +
        ((h 0 1 : ℂ) - Complex.I * (h 1 1 : ℂ))) /
      (((h 0 0 : ℂ) + Complex.I * (h 1 0 : ℂ)) * (z : ℂ) +
        ((h 0 1 : ℂ) + Complex.I * (h 1 1 : ℂ))) := by
  have hd := cayleySL_action_den_ne_zero h z
  rw [upperHalfPlaneCayley, cayleySL_action_formula, div_sub' hd,
    div_add' _ _ _ hd, div_div_div_cancel_right₀ hd]
  congr 1 <;> ring

/-- Factoring the literal rational formula by the nonzero UHP input exposes
the actual endpoint at infinity without an abstract boundary action. -/
theorem upperHalfPlaneCayley_smul_inv_form (h : SL(2, ℝ)) (z : UpperHalfPlane) :
    upperHalfPlaneCayley (h • z) =
      (((h 0 0 : ℂ) - Complex.I * (h 1 0 : ℂ)) +
        ((h 0 1 : ℂ) - Complex.I * (h 1 1 : ℂ)) / (z : ℂ)) /
      (((h 0 0 : ℂ) + Complex.I * (h 1 0 : ℂ)) +
        ((h 0 1 : ℂ) + Complex.I * (h 1 1 : ℂ)) / (z : ℂ)) := by
  rw [upperHalfPlaneCayley_smul,
    ← div_div_div_cancel_right₀ z.ne_zero]
  congr 1 <;> rw [add_div, mul_div_cancel_right₀ _ z.ne_zero]

/-- The actual SL/Cayley composite tends to its zero-column endpoint whenever
the actual upper-half-plane input tends to zero in the ambient complex plane. -/
theorem upperHalfPlaneCayley_smul_tendsto_zero
    {α : Type*} {l : Filter α} (h : SL(2, ℝ)) (γ : α → UpperHalfPlane)
    (hγ : Tendsto (fun t => (γ t : ℂ)) l (𝓝 0)) :
    Tendsto (fun t => upperHalfPlaneCayley (h • γ t)) l
      (𝓝 (upperHalfPlaneCayleySLZero h)) := by
  have hn : Tendsto (fun t =>
      ((h 0 0 : ℂ) - Complex.I * (h 1 0 : ℂ)) * (γ t : ℂ) +
        ((h 0 1 : ℂ) - Complex.I * (h 1 1 : ℂ))) l
      (𝓝 ((h 0 1 : ℂ) - Complex.I * (h 1 1 : ℂ))) := by
    simpa only [mul_zero, zero_add] using
      (hγ.const_mul ((h 0 0 : ℂ) - Complex.I * (h 1 0 : ℂ))).add_const
        ((h 0 1 : ℂ) - Complex.I * (h 1 1 : ℂ))
  have hd : Tendsto (fun t =>
      ((h 0 0 : ℂ) + Complex.I * (h 1 0 : ℂ)) * (γ t : ℂ) +
        ((h 0 1 : ℂ) + Complex.I * (h 1 1 : ℂ))) l
      (𝓝 ((h 0 1 : ℂ) + Complex.I * (h 1 1 : ℂ))) := by
    simpa only [mul_zero, zero_add] using
      (hγ.const_mul ((h 0 0 : ℂ) + Complex.I * (h 1 0 : ℂ))).add_const
        ((h 0 1 : ℂ) + Complex.I * (h 1 1 : ℂ))
  simp_rw [upperHalfPlaneCayley_smul]
  exact hn.div hd (upperHalfPlaneCayleySLZero_den_ne_zero h)

/-- Factoring by the actual nonzero input gives the infinity-column endpoint
when the input complex norm tends to infinity. No boundary action is assumed. -/
theorem upperHalfPlaneCayley_smul_tendsto_infinity
    {α : Type*} {l : Filter α} (h : SL(2, ℝ)) (γ : α → UpperHalfPlane)
    (hγ : Tendsto (fun t => ‖(γ t : ℂ)‖) l atTop) :
    Tendsto (fun t => upperHalfPlaneCayley (h • γ t)) l
      (𝓝 (upperHalfPlaneCayleySLInfinity h)) := by
  have hi : Tendsto (fun t => (γ t : ℂ)⁻¹) l (𝓝 0) :=
    tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp hγ)
  have hn : Tendsto (fun t =>
      ((h 0 0 : ℂ) - Complex.I * (h 1 0 : ℂ)) +
        ((h 0 1 : ℂ) - Complex.I * (h 1 1 : ℂ)) / (γ t : ℂ)) l
      (𝓝 ((h 0 0 : ℂ) - Complex.I * (h 1 0 : ℂ))) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      (tendsto_const_nhds (x := (h 0 0 : ℂ) - Complex.I * (h 1 0 : ℂ))).add
        (hi.const_mul ((h 0 1 : ℂ) - Complex.I * (h 1 1 : ℂ)))
  have hd : Tendsto (fun t =>
      ((h 0 0 : ℂ) + Complex.I * (h 1 0 : ℂ)) +
        ((h 0 1 : ℂ) + Complex.I * (h 1 1 : ℂ)) / (γ t : ℂ)) l
      (𝓝 ((h 0 0 : ℂ) + Complex.I * (h 1 0 : ℂ))) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      (tendsto_const_nhds (x := (h 0 0 : ℂ) + Complex.I * (h 1 0 : ℂ))).add
        (hi.const_mul ((h 0 1 : ℂ) + Complex.I * (h 1 1 : ℂ)))
  simp_rw [upperHalfPlaneCayley_smul_inv_form]
  exact hn.div hd (upperHalfPlaneCayleySLInfinity_den_ne_zero h)

/-- Uniform closeness to a positive-speed vertical curve gives the actual
negative endpoint in any one fixed SL/Cayley chart. -/
theorem upperHalfPlaneCayley_smul_tendsto_atBot_of_dist_vertical
    (h : SL(2, ℝ)) (γ : ℝ → UpperHalfPlane) (k B : ℝ) (hk : 0 < k)
    (hbound : ∀ t, dist (γ t) (hyperbolicVerticalAxis (k * t)) ≤ B) :
    Tendsto (fun t => upperHalfPlaneCayley (h • γ t)) atBot
      (𝓝 (upperHalfPlaneCayleySLZero h)) := by
  apply upperHalfPlaneCayley_smul_tendsto_zero h γ
  have hkt : Tendsto (fun t : ℝ => k * t) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos hk).mpr tendsto_id
  have hexp : Tendsto (fun t : ℝ => Real.exp (k * t) * Real.exp B) atBot (𝓝 0) := by
    simpa only [zero_mul] using (Real.tendsto_exp_atBot.comp hkt).mul_const (Real.exp B)
  exact squeeze_zero_norm (fun t =>
    upperHalfPlane_complex_norm_le_of_dist_vertical (γ t) (k * t) B (hbound t)) hexp

/-- The corresponding actual positive endpoint in that same fixed chart.
No continuity of the curve or abstract compactification is required. -/
theorem upperHalfPlaneCayley_smul_tendsto_atTop_of_dist_vertical
    (h : SL(2, ℝ)) (γ : ℝ → UpperHalfPlane) (k B : ℝ) (hk : 0 < k)
    (hbound : ∀ t, dist (γ t) (hyperbolicVerticalAxis (k * t)) ≤ B) :
    Tendsto (fun t => upperHalfPlaneCayley (h • γ t)) atTop
      (𝓝 (upperHalfPlaneCayleySLInfinity h)) := by
  apply upperHalfPlaneCayley_smul_tendsto_infinity h γ
  have hkt : Tendsto (fun t : ℝ => k * t) atTop atTop := tendsto_id.const_mul_atTop hk
  have hexp : Tendsto (fun t : ℝ => Real.exp (k * t) / Real.exp B) atTop atTop :=
    (Real.tendsto_exp_atTop.comp hkt).atTop_div_const (Real.exp_pos B)
  apply tendsto_atTop_mono (fun t => ?_) hexp
  exact (upperHalfPlane_im_lower_of_dist_vertical (γ t) (k * t) B (hbound t)).trans
    (Complex.im_le_norm (γ t : ℂ))

end Markov
