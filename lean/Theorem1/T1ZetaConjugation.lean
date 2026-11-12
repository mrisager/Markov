import T1ReciprocalZeta
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Analytic.Uniqueness

/-! Complex conjugation of actual zeta on the pinned library, using the
Dirichlet series and the entire function after removing the simple pole. -/

namespace Markov
open Complex Filter Set
open scoped ComplexConjugate Topology

private theorem zeta_conj_right {s : ℂ} (hs : 1 < s.re) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs),
    zeta_eq_tsum_one_div_nat_add_one_cpow hs, Complex.conj_tsum]
  apply tsum_congr
  intro n
  have hn : (0 : ℝ) ≤ (n + 1 : ℝ) := by positivity
  have hp : (n + 1 : ℂ) ^ conj s = conj ((n + 1 : ℂ) ^ s) := by
    have ha : (n + 1 : ℂ).arg = 0 := by
      rw [show (n + 1 : ℂ) = ((n + 1 : ℝ) : ℂ) by push_cast; rfl]
      exact Complex.arg_ofReal_of_nonneg hn
    have hc : conj (n + 1 : ℂ) = (n + 1 : ℂ) := by simp
    rw [Complex.cpow_conj _ _ (by rw [ha]; exact Real.pi_pos.ne), hc]
  simp [hp, one_div]

private theorem conjugate_ne_one {s : ℂ} (hs : s ≠ 1) : conj s ≠ 1 := by
  intro h
  apply hs
  simpa only [Complex.conj_conj, map_one] using congrArg (conj : ℂ → ℂ) h

/-- Actual entire pole-removed zeta commutes with complex conjugation. -/
theorem t1_poleRemovedZeta_conj (s : ℂ) :
    t1_poleRemovedZeta (conj s) = conj (t1_poleRemovedZeta s) := by
  let F : ℂ → ℂ := conj ∘ t1_poleRemovedZeta ∘ conj
  have hF : Differentiable ℂ F := by
    intro z
    simpa only [Complex.conj_conj] using
      (t1_poleRemovedZeta_differentiable (conj z)).conj_conj
  have he : F =ᶠ[𝓝 (2 : ℂ)] t1_poleRemovedZeta := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num)] with z hz
    have h : z ≠ 1 := by
      intro hz'
      subst z
      norm_num at hz
    have hc := conjugate_ne_one h
    simp only [F, Function.comp_apply, t1_poleRemovedZeta,
      Function.update_of_ne h, Function.update_of_ne hc, zeta_conj_right hz,
      map_mul, map_sub, map_one, Complex.conj_conj]
  have hF' : AnalyticOnNhd ℂ F univ := fun z _ => hF.analyticAt z
  have hZ : AnalyticOnNhd ℂ t1_poleRemovedZeta univ :=
    fun z _ => t1_poleRemovedZeta_differentiable.analyticAt z
  have h := hF'.eqOn_of_preconnected_of_eventuallyEq
    hZ isPreconnected_univ (mem_univ (2 : ℂ)) he
    (mem_univ (conj s))
  simpa [F] using h.symm

/-- The actual Riemann zeta function commutes with conjugation away from its pole. -/
theorem t1_riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  have hc := conjugate_ne_one hs
  have h := t1_poleRemovedZeta_conj s
  simp only [t1_poleRemovedZeta, Function.update_of_ne hs, Function.update_of_ne hc,
    map_mul, map_sub, map_one] at h
  exact mul_left_cancel₀ (sub_ne_zero.mpr hc) h

end Markov
