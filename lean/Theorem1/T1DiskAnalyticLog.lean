import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! A normalized analytic logarithm on a genuine complex disk, obtained
by integrating the logarithmic derivative. -/
noncomputable section
open Set Metric Complex
namespace Markov

theorem t1_disk_normalized_log {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball 0 r))
    (hn : ∀ z ∈ ball 0 r, f z ≠ 0) :
    ∃ g : ℂ → ℂ, g 0 = 0 ∧ DifferentiableOn ℂ g (ball 0 r) ∧
      ∀ z ∈ ball 0 r, Complex.exp (g z) = f z/f 0 := by
  have hlogDeriv := (hf.deriv isOpen_ball).div hf hn
  obtain ⟨p,hp⟩ := hlogDeriv.isExactOn_ball
  let g := fun z => p z - p 0
  have h0 : g 0 = 0 := sub_self _
  have hg : ∀ z ∈ ball 0 r, HasDerivAt g (deriv f z/f z) z :=
    fun z hz => (hp z hz).sub_const (p 0)
  let F := fun z => f z * Complex.exp (-g z)
  have hF : ∀ z ∈ ball 0 r, HasDerivAt F 0 z := by
    intro z hz
    have h := (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.mul
      ((hg z hz).neg.cexp)
    convert h using 1
    field_simp [hn z hz]
    ring
  have hF' : DifferentiableOn ℂ F (ball 0 r) :=
    fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
  refine ⟨g,h0,fun z hz => (hg z hz).differentiableAt.differentiableWithinAt,?_⟩
  intro z hz
  have hz0 : (0 : ℂ) ∈ ball 0 r := mem_ball_self hr
  have he := isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball (0 : ℂ) r).isPreconnected
    hF' (fun w hw => by rw [(hF w hw).hasFDerivAt.fderiv]; simp) hz hz0
  change f z * Complex.exp (-g z) = f 0 * Complex.exp (-g 0) at he
  rw [h0,neg_zero,Complex.exp_zero,mul_one,Complex.exp_neg] at he
  have he' := (mul_inv_eq_iff_eq_mul₀ (Complex.exp_ne_zero _)).mp he
  exact (eq_div_iff (hn 0 hz0)).2 (by rw [mul_comm]; exact he'.symm)

end Markov
