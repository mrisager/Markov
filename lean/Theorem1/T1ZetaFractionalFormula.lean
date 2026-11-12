import T1ReciprocalZeta
import T1ZetaFractionalBound
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.Complex.Convex

/-! The actual pole-removed zeta function equals its bounded
fractional-part integral formula throughout Re(s)>0. -/
noncomputable section
open Set Complex Filter MeasureTheory Asymptotics
open scoped Topology
namespace Markov

theorem t1_zeta_fractional_formula_right {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s/(s-1)-s*t1_zetaFractionalMellin s := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖(1 : ℂ)‖) =O[atTop]
      (fun n : ℕ => (n : ℝ)^(1 : ℝ)) := by
    simpa using (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)
  have h := LSeries_eq_mul_integral' (1 : ℕ → ℂ) zero_le_one hs hO
  rw [LSeries_one_eq_riemannZeta hs] at h
  have hsum (n : ℕ) : (∑ k ∈ Finset.Icc 1 n, (1 : ℕ → ℂ) k) = (n : ℂ) := by simp
  simp_rw [hsum] at h
  have heq :
      (∫ x : ℝ in Ioi (1 : ℝ), (⌊x⌋₊ : ℂ)*(x : ℂ)^(-(s+1))) =
      ∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ)^(-s) -
        (↑(Int.fract x : ℝ) : ℂ)*(x : ℂ)^(-(s+1)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hcast : (⌊x⌋₊ : ℂ) = (x : ℂ) - (↑(Int.fract x : ℝ) : ℂ) := by
      norm_cast
      rw [Int.fract,sub_sub_cancel]
      exact_mod_cast Int.natCast_floor_eq_floor hx0.le
    have hp : (x : ℂ)*(x : ℂ)^(-(s+1)) = (x : ℂ)^(-s) := by
      nth_rw 1 [← Complex.cpow_one (x : ℂ)]
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx0.ne'),
        show 1+(-(s+1)) = -s by ring]
    dsimp only
    rw [hcast,sub_mul,hp]
  rw [heq,integral_sub
    (integrableOn_Ioi_cpow_of_lt (a := -s) (by simpa only [neg_re,neg_lt_neg_iff] using hs)
      (show (0 : ℝ)<1 by norm_num))
    (t1_zetaFractional_integrable (by linarith : 0 < s.re)),
    ← t1_zetaFractionalMellin_integral,
    integral_Ioi_cpow_of_lt (a := -s) (by simpa only [neg_re,neg_lt_neg_iff] using hs)
      (show (0 : ℝ)<1 by norm_num)] at h
  rw [ofReal_one,Complex.one_cpow,show -s+1 = -(s-1) by ring,div_neg,neg_div,neg_neg,
    mul_sub,mul_one_div] at h
  exact h

theorem t1_poleRemovedZeta_fractional_formula {s : ℂ} (hs : 0 < s.re) :
    t1_poleRemovedZeta s = s-s*(s-1)*t1_zetaFractionalMellin s := by
  let U := {z : ℂ | 0 < z.re}
  let G := fun z : ℂ => z-z*(z-1)*t1_zetaFractionalMellin z
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hconn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hG : DifferentiableOn ℂ G U := by
    intro z hz
    exact (differentiableAt_id.sub (((differentiableAt_id.mul
      (differentiableAt_id.sub_const 1))).mul
      (t1_zetaFractionalMellin_differentiableAt hz))).differentiableWithinAt
  have hnear : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), t1_poleRemovedZeta z = G z := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num)] with z hz
    have hz' : 1 < z.re := hz
    have hn : z ≠ 1 := by rintro rfl; norm_num at hz'
    simp only [t1_poleRemovedZeta,Function.update_of_ne hn,G,t1_zeta_fractional_formula_right hz']
    field_simp [sub_ne_zero.mpr hn]
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (t1_poleRemovedZeta_differentiable.differentiableOn.analyticOnNhd hU)
    (hG.analyticOnNhd hU) hconn
      (show (2 : ℂ) ∈ U by norm_num [U]) hnear hs

end Markov
