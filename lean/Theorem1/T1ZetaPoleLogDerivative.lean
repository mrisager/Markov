import T1VKRegion
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Uniform real-axis logarithmic derivative after removing the genuine
simple pole. The finite constant is obtained by continuity on the actual
closed interval, including its left endpoint. -/

namespace Markov
open Complex Filter Set
open scoped Topology

theorem t1_logDeriv_riemannZeta_of_ne_one {s : ℂ}
    (hs : s ≠ 1) (hP : t1_poleRemovedZeta s ≠ 0) :
    logDeriv riemannZeta s = logDeriv t1_poleRemovedZeta s - 1/(s-1) := by
  have he : riemannZeta =ᶠ[𝓝 s] (fun z => t1_poleRemovedZeta z / (z-1)) := by
    filter_upwards [(show IsOpen {z : ℂ | z ≠ 1} from isOpen_ne).mem_nhds hs] with z hz
    change z ≠ 1 at hz
    simp only [t1_poleRemovedZeta, Function.update_of_ne hz]
    rw [mul_comm (z-1), mul_div_cancel_right₀ _ (sub_ne_zero.mpr hz)]
  calc
    _ = logDeriv (fun z => t1_poleRemovedZeta z / (z-1)) s := by
      rw [logDeriv_apply,logDeriv_apply,he.deriv_eq,he.eq_of_nhds]
    _ = _ := by
      rw [logDeriv_div (g := fun z : ℂ => z-1) s hP (sub_ne_zero.mpr hs)
        (t1_poleRemovedZeta_differentiable s) (by fun_prop)]
      simp [logDeriv_apply]

theorem t1_neg_logDeriv_zeta_real_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      (-logDeriv riemannZeta (((1+x : ℝ) : ℂ)) ).re ≤ 1/x+C := by
  let P := t1_poleRemovedZeta
  let F : ℝ → ℂ := fun x => ((1+x : ℝ) : ℂ)
  have hF : Continuous F := by fun_prop
  have hP : Continuous P := t1_poleRemovedZeta_differentiable.continuous
  have hdP : Continuous (deriv P) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((t1_poleRemovedZeta_differentiable.analyticAt z).deriv).continuousAt
  have hn (x : ℝ) (hx : 0 ≤ x) : P (F x) ≠ 0 :=
    t1_poleRemovedZeta_ne_zero_of_one_le_re (by simp [F,hx])
  let f : ℝ → ℝ := fun x => (-(deriv P (F x) / P (F x))).re
  have hf : ContinuousOn f (Icc 0 1) := by
    apply Complex.continuous_re.comp_continuousOn
    apply ContinuousOn.neg
    exact (hdP.comp hF).continuousOn.div (hP.comp hF).continuousOn (fun x hx => hn x hx.1)
  obtain ⟨K,hK⟩ := isCompact_Icc.bddAbove_image hf
  refine ⟨max 0 K,le_max_left _ _,fun x hx hxu => ?_⟩
  have hs : F x ≠ 1 := by
    intro he
    have h := congrArg Complex.re he
    simp [F] at h
    linarith
  have hcomp := t1_logDeriv_riemannZeta_of_ne_one hs (hn x hx.le)
  have hxcomp : F x - 1 = (x : ℂ) := by
    simp only [F,Complex.ofReal_add,Complex.ofReal_one]
    ring
  have hbound := (hK (show f x ∈ f '' Icc 0 1 from ⟨x,⟨hx.le,hxu⟩,rfl⟩)).trans
    (le_max_right (0 : ℝ) K)
  change (-logDeriv riemannZeta (F x)).re ≤ 1/x + max 0 K
  rw [hcomp,hxcomp,← Complex.ofReal_one,← Complex.ofReal_div]
  simp only [Complex.neg_re,Complex.sub_re,Complex.ofReal_re,logDeriv_apply]
  change -((deriv P (F x) / P (F x)).re - 1/x) ≤ _
  change -(deriv P (F x) / P (F x)).re ≤ _ at hbound
  linarith only [hbound]

end Markov
