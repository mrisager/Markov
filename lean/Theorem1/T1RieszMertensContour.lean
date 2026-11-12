import T1RieszStripIntegrand

/-! Shift the actual smoothed Möbius integral to the left edge of a
polynomially bounded strip, with verified uniform horizontal decay. -/
noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology
namespace Markov

theorem t1_rieszIntegrand_shift {F : ℂ → ℂ} {σ : ℝ} (hσ : (1 : ℝ)/2 ≤ σ) (hσ2 : σ ≤ 2)
    {k : ℕ} {x C A : ℝ} (hx : 1 ≤ x) (hC : 0 ≤ C) (hk : A < (k : ℝ))
    (hF : DifferentiableOn ℂ F {s : ℂ | s.re ∈ Icc σ 2})
    (hB : ∀ s : ℂ, s.re ∈ Icc σ 2 → ‖F s‖ ≤ C*(1+|s.im|)^A) :
    (∫ t : ℝ, t1_rieszIntegrand k x F (t1_verticalPoint 2 t)) =
      ∫ t : ℝ, t1_rieszIntegrand k x F (t1_verticalPoint σ t) := by
  have hx0 := zero_lt_one.trans_le hx
  let p := A-((k : ℝ)+1)
  have hp : 0 < -p := by dsimp [p]; linarith
  let g := fun T : ℝ => (x^2*C*(3 : ℝ)^(k+1))*(1+|T|)^p
  have hu : Tendsto (fun T : ℝ => 1+|T|) atTop atTop := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [eventually_ge_atTop (max 0 b)] with T hT
    rw [abs_of_nonneg ((le_max_left _ _).trans hT)]
    linarith [(le_max_right 0 b).trans hT]
  have hg : Tendsto g atTop (𝓝 0) := by
    simpa only [g,Function.comp_def,neg_neg,mul_zero] using
      ((tendsto_rpow_neg_atTop hp).comp hu).const_mul (x^2*C*(3 : ℝ)^(k+1))
  apply t1_vertical_integral_shift hσ2 (t1_rieszIntegrand_differentiableOn hσ hx0 hF)
    (t1_rieszIntegrand_verticalIntegrable hσ hx0 hC hk ⟨le_rfl,hσ2⟩ hF hB)
    (t1_rieszIntegrand_verticalIntegrable hσ hx0 hC hk ⟨hσ2,le_rfl⟩ hF hB) hg
  have hnorm (ξ t : ℝ) (hξ : ξ ∈ Icc σ 2) :
      ‖t1_rieszIntegrand k x F (t1_verticalPoint ξ t)‖ ≤ g t := by
    have hRe := t1_verticalPoint_re ξ t
    have hm : (t1_verticalPoint ξ t).re ∈ Icc σ 2 := by rwa [hRe]
    have hb := t1_rieszIntegrand_norm_le hx0 hC (hσ.trans hm.1) (hB _ hm) (k := k)
    rw [hRe,t1_verticalPoint_im] at hb
    refine hb.trans ?_
    have hpow : x^ξ ≤ x^2 := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_le hx hξ.2
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow hC) (by positivity)) (by positivity)
  exact Eventually.of_forall fun T ξ hξ =>
    ⟨hnorm ξ T hξ,by simpa only [g,abs_neg] using hnorm ξ (-T) hξ⟩

theorem t1_rieszMertens_integral_on_strip {σ : ℝ} (hσ : (1 : ℝ)/2 ≤ σ) (hσ2 : σ ≤ 2)
    {k : ℕ} (hk : 0 < k) {x C A : ℝ} (hx : 1 ≤ x) (hC : 0 ≤ C) (hAk : A < (k : ℝ))
    (hF : DifferentiableOn ℂ t1_reciprocalZeta {s : ℂ | s.re ∈ Icc σ 2})
    (hB : ∀ s : ℂ, s.re ∈ Icc σ 2 → ‖t1_reciprocalZeta s‖ ≤ C*(1+|s.im|)^A) :
    (t1_rieszMertens k x : ℂ) = (x : ℂ)^k/(↑(2*Real.pi) : ℂ) *
      ∫ t : ℝ, t1_rieszIntegrand k x t1_reciprocalZeta (t1_verticalPoint σ t) := by
  rw [t1_rieszMertens_integral_line_two hk (zero_lt_one.trans_le hx),
    t1_rieszIntegrand_shift hσ hσ2 hx hC hAk hF hB]

end Markov
