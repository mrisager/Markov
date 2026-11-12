import T1DiskAnalyticLog

/-! Borel–Carathéodory bounds the reciprocal of a nonvanishing
holomorphic function on a smaller disk. -/
noncomputable section
open Set Metric Complex
namespace Markov

theorem t1_disk_reciprocal_bound {f : ℂ → ℂ} {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball 0 r)) (hn : ∀ w ∈ ball 0 r, f w ≠ 0)
    (hbound : ∀ w ∈ ball 0 r, ‖f w/f 0‖ < Real.exp M)
    {z : ℂ} (hz : z ∈ ball 0 r) :
    ‖(f z)⁻¹‖ ≤ ‖(f 0)⁻¹‖ * Real.exp (2*M*‖z‖/(r-‖z‖)) := by
  obtain ⟨g,hg0,hg,hexp⟩ := t1_disk_normalized_log hr hf hn
  have hgRe : MapsTo g (ball 0 r) {w : ℂ | w.re < M} := by
    intro w hw
    apply Real.exp_lt_exp.mp
    rw [← Complex.norm_exp, hexp w hw]
    exact hbound w hw
  have hgNorm := borelCaratheodory_zero hM hg hgRe hr hz hg0
  have hn0 := hn 0 (mem_ball_self hr)
  have he : (f z)⁻¹ = (f 0)⁻¹ * Complex.exp (-g z) := by
    rw [Complex.exp_neg,hexp z hz]
    field_simp [hn z hz,hn0]
  rw [he,norm_mul,Complex.norm_exp,Complex.neg_re]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  exact ((neg_le_abs (g z).re).trans (Complex.abs_re_le_norm _)).trans hgNorm

end Markov
