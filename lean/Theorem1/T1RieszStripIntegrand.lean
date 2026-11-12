import T1RieszMertensInversion
import T1VerticalContourShift

/-! Uniform bounds on the actual Riesz integrand on a closed strip. -/
noncomputable section
open Complex MeasureTheory Set
namespace Markov

theorem t1_rieszIntegrand_differentiableOn {F : ℂ → ℂ} {σ : ℝ}
    (hσ : (1 : ℝ)/2 ≤ σ) {k : ℕ} {x : ℝ} (hx : 0 < x)
    (hF : DifferentiableOn ℂ F {s : ℂ | s.re ∈ Icc σ 2}) :
    DifferentiableOn ℂ (t1_rieszIntegrand k x F) {s : ℂ | s.re ∈ Icc σ 2} := by
  have hp : Differentiable ℂ (fun s : ℂ => (x : ℂ)^s) :=
    differentiable_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hden : DifferentiableOn ℂ (fun s => (t1_rieszDenom k s)⁻¹) {s : ℂ | s.re ∈ Icc σ 2} :=
    (t1_rieszDenom_differentiable k).differentiableOn.inv (fun s hs =>
      t1_rieszDenom_ne_zero k (lt_of_lt_of_le (by linarith : 0 < σ) hs.1))
  exact (hp.differentiableOn.mul hF).mul hden

theorem t1_rieszIntegrand_norm_le {F : ℂ → ℂ} {k : ℕ} {x C A : ℝ} (hx : 0 < x) (hC : 0 ≤ C)
    {s : ℂ} (hs : (1 : ℝ)/2 ≤ s.re) (hF : ‖F s‖ ≤ C*(1+|s.im|)^A) :
    ‖t1_rieszIntegrand k x F s‖ ≤
      (x^s.re*C*(3 : ℝ)^(k+1))*(1+|s.im|)^(A-((k : ℝ)+1)) := by
  let u := 1+|s.im|
  have hu : 0 < u := by dsimp [u]; positivity
  simp only [t1_rieszIntegrand,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  calc
    _ ≤ (x^s.re*(C*u^A))*((3 : ℝ)^(k+1)*u^(-((k : ℝ)+1))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hF (Real.rpow_nonneg hx.le _))
        (t1_rieszDenom_inv_norm_le k hs) (norm_nonneg _)
        (mul_nonneg (Real.rpow_nonneg hx.le _) (mul_nonneg hC (Real.rpow_nonneg hu.le _)))
    _ = _ := by
      change _ = (x^s.re*C*(3 : ℝ)^(k+1))*u^(A-((k : ℝ)+1))
      rw [sub_eq_add_neg,Real.rpow_add hu]
      ring

theorem t1_rieszIntegrand_verticalIntegrable {F : ℂ → ℂ} {σ : ℝ}
    (hσ : (1 : ℝ)/2 ≤ σ) {k : ℕ} {x C A ξ : ℝ} (hx : 0 < x)
    (hC : 0 ≤ C) (hk : A < (k : ℝ)) (hξ : ξ ∈ Icc σ 2)
    (hF : DifferentiableOn ℂ F {s : ℂ | s.re ∈ Icc σ 2})
    (hB : ∀ s : ℂ, s.re ∈ Icc σ 2 → ‖F s‖ ≤ C*(1+|s.im|)^A) :
    VerticalIntegrable (t1_rieszIntegrand k x F) ξ := by
  have hc := (t1_rieszIntegrand_differentiableOn hσ (k := k) hx hF).continuousOn.comp_continuous
    (t1_verticalPoint_continuous ξ) (fun t => by
      change (t1_verticalPoint ξ t).re ∈ Icc σ 2
      rwa [t1_verticalPoint_re])
  have hi := (t1_verticalPower_integrable (A-((k : ℝ)+1)) (by linarith)).const_mul
    (x^ξ*C*(3 : ℝ)^(k+1))
  refine hi.mono' hc.aestronglyMeasurable ?_
  filter_upwards with t
  have hRe := t1_verticalPoint_re ξ t
  have hm : (t1_verticalPoint ξ t).re ∈ Icc σ 2 := by rwa [hRe]
  simpa only [hRe,t1_verticalPoint_im] using t1_rieszIntegrand_norm_le hx hC
    (hσ.trans hm.1) (hB _ hm) (k := k)

end Markov
