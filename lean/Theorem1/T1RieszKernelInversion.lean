import T1RieszDenominator

/-! Exact Mellin inversion of the genuine continuous Riesz weight. -/
noncomputable section
open Complex MeasureTheory
namespace Markov

def t1_verticalPoint (σ t : ℝ) : ℂ := (σ : ℂ)+(t : ℂ)*I

theorem t1_verticalPoint_re (σ t : ℝ) : (t1_verticalPoint σ t).re = σ := by
  simp [t1_verticalPoint]

theorem t1_verticalPoint_im (σ t : ℝ) : (t1_verticalPoint σ t).im = t := by
  simp [t1_verticalPoint]

theorem t1_verticalPoint_continuous (σ : ℝ) : Continuous (t1_verticalPoint σ) := by
  unfold t1_verticalPoint
  fun_prop

theorem t1_rieszKernel_inversion {k : ℕ} (hk : 0 < k) {σ : ℝ} (hσ : (1 : ℝ)/2 ≤ σ)
    {u : ℝ} (hu : 0 < u) :
    (∫ t : ℝ, (u : ℂ)^(-t1_verticalPoint σ t) * (t1_rieszDenom k (t1_verticalPoint σ t))⁻¹) =
      (↑(2*Real.pi) : ℂ)*t1_rieszKernel k u := by
  have hσ0 : 0 < σ := by linarith
  have hm (t : ℝ) : mellin (t1_rieszKernel k) (t1_verticalPoint σ t) =
      (t1_rieszDenom k (t1_verticalPoint σ t))⁻¹ := by
    rw [← one_div]
    exact (t1_rieszKernel_hasMellin hk (by rwa [t1_verticalPoint_re])).2
  have hi : VerticalIntegrable (mellin (t1_rieszKernel k)) σ := by
    have h := t1_rieszDenom_inv_verticalIntegrable hk hσ
    change Integrable (fun t => (t1_rieszDenom k (t1_verticalPoint σ t))⁻¹) at h
    change Integrable (fun t => mellin (t1_rieszKernel k) (t1_verticalPoint σ t))
    simpa only [hm] using h
  have h := mellinInv_mellin_eq σ (t1_rieszKernel k) hu
    (t1_rieszKernel_hasMellin hk (show 0 < (σ : ℂ).re by simpa)).1
    hi (t1_rieszKernel_continuous k).continuousAt
  change (1/(2*Real.pi)) • (∫ t : ℝ, (u : ℂ)^(-t1_verticalPoint σ t) •
    mellin (t1_rieszKernel k) (t1_verticalPoint σ t)) = t1_rieszKernel k u at h
  simp only [hm,smul_eq_mul,Complex.real_smul,one_div,Complex.ofReal_inv] at h
  exact (inv_mul_eq_iff_eq_mul₀ (by exact_mod_cast (show 2*Real.pi ≠ 0 by positivity))).mp h

end Markov
