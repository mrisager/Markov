import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

/-! The spatial cap estimate uses both the normal/support-point association and
its depth bounds explicitly. It does not establish the geometric hypotheses
needed to apply the estimate to any particular convex curve. -/

noncomputable section

namespace Markov

/-- In a Euclidean plane, two orthogonal unit vectors control distance by the
sum of the absolute values of the two coordinates. -/
theorem euclideanPlane_norm_le_orthogonal_coordinates
    (θ e v : EuclideanSpace ℝ (Fin 2))
    (hθ : ‖θ‖ = 1) (he : ‖e‖ = 1) (horth : inner ℝ θ e = 0) :
    ‖v‖ ≤ |inner ℝ v θ| + |inner ℝ v e| := by
  let u : Fin 2 → EuclideanSpace ℝ (Fin 2) := ![θ, e]
  have horth' : inner ℝ e θ = 0 := by rw [real_inner_comm]; exact horth
  have hon : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [u, hθ, he, horth, horth']
  let b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
    OrthonormalBasis.mk hon
      (hon.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge
  have hb (i : Fin 2) : b i = u i := by
    exact congrFun (OrthonormalBasis.coe_mk hon _) i
  have hv : inner ℝ v θ • θ + inner ℝ v e • e = v := by
    simpa [Fin.sum_univ_two, hb, u, real_inner_comm] using b.sum_repr' v
  calc
    ‖v‖ = ‖inner ℝ v θ • θ + inner ℝ v e • e‖ := congrArg norm hv.symm
    _ ≤ ‖inner ℝ v θ • θ‖ + ‖inner ℝ v e • e‖ := norm_add_le _ _
    _ = _ := by simp [norm_smul, hθ, he, Real.norm_eq_abs]

/-- A rectangle with longitudinal width `δ` and transverse brackets `lo, hi`
has diameter at most the sum of its two side lengths. -/
theorem euclideanPlane_diam_le_of_coordinate_brackets
    (S : Set (EuclideanSpace ℝ (Fin 2))) (θ e : EuclideanSpace ℝ (Fin 2))
    (δ lo hi : ℝ) (hθ : ‖θ‖ = 1) (he : ‖e‖ = 1)
    (horth : inner ℝ θ e = 0) (hδ : 0 ≤ δ) (hlohi : lo ≤ hi)
    (hwidth : ∀ x ∈ S, ∀ y ∈ S, |inner ℝ (x - y) θ| ≤ δ)
    (hbracket : ∀ z ∈ S, lo ≤ inner ℝ z e ∧ inner ℝ z e ≤ hi) :
    Metric.diam S ≤ hi - lo + δ := by
  apply Metric.diam_le_of_forall_dist_le (by linarith)
  intro x hx y hy
  have hxbr := hbracket x hx
  have hybr := hbracket y hy
  have hewidth : |inner ℝ (x - y) e| ≤ hi - lo := by
    rw [inner_sub_left, abs_le]
    constructor <;> linarith
  calc
    dist x y = ‖x - y‖ := dist_eq_norm _ _
    _ ≤ |inner ℝ (x - y) θ| + |inner ℝ (x - y) e| :=
      euclideanPlane_norm_le_orthogonal_coordinates θ e (x - y) hθ he horth
    _ ≤ δ + (hi - lo) := add_le_add (hwidth x hx y hy) hewidth
    _ = hi - lo + δ := by ring

/-- The upper supporting line with normal `c • θ + s • e` supplies the upper
transverse bracket, and the lower line with normal `c • θ - s • e` the lower
bracket. Both depth bounds refer to their associated supporting points. -/
theorem euclideanCap_transverse_brackets
    (θ e aMinus aPlus z : EuclideanSpace ℝ (Fin 2)) (δ c s : ℝ)
    (hc : 0 ≤ c) (hs : 0 < s)
    (hplus : inner ℝ (z - aPlus) (c • θ + s • e) ≤ 0)
    (hminus : inner ℝ (z - aMinus) (c • θ - s • e) ≤ 0)
    (hdepthPlus : -δ ≤ inner ℝ (z - aPlus) θ)
    (hdepthMinus : -δ ≤ inner ℝ (z - aMinus) θ) :
    inner ℝ aMinus e - δ * (c / s) ≤ inner ℝ z e ∧
      inner ℝ z e ≤ inner ℝ aPlus e + δ * (c / s) := by
  simp only [inner_add_right, inner_sub_right, inner_smul_right,
    inner_sub_left] at hplus hminus hdepthPlus hdepthMinus
  have hdPlus := mul_le_mul_of_nonneg_left hdepthPlus hc
  have hdMinus := mul_le_mul_of_nonneg_left hdepthMinus hc
  constructor
  · apply (mul_le_mul_iff_right₀ hs).mp
    have hdiv : s * (inner ℝ aMinus e - δ * (c / s)) =
        s * inner ℝ aMinus e - δ * c := by field_simp
    rw [hdiv]
    nlinarith
  · apply (mul_le_mul_iff_right₀ hs).mp
    have hdiv : s * (inner ℝ aPlus e + δ * (c / s)) =
        s * inner ℝ aPlus e + δ * c := by field_simp
    rw [hdiv]
    nlinarith

/-- Generic spatial estimate from two associated supporting lines, two depth
bounds, and a longitudinal width bound. -/
theorem euclideanCap_diam_le
    (S : Set (EuclideanSpace ℝ (Fin 2)))
    (θ e aMinus aPlus : EuclideanSpace ℝ (Fin 2)) (δ c s : ℝ)
    (hθ : ‖θ‖ = 1) (he : ‖e‖ = 1) (horth : inner ℝ θ e = 0)
    (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hs : 0 < s)
    (hplus : ∀ z ∈ S, inner ℝ (z - aPlus) (c • θ + s • e) ≤ 0)
    (hminus : ∀ z ∈ S, inner ℝ (z - aMinus) (c • θ - s • e) ≤ 0)
    (hdepthPlus : ∀ z ∈ S, -δ ≤ inner ℝ (z - aPlus) θ)
    (hdepthMinus : ∀ z ∈ S, -δ ≤ inner ℝ (z - aMinus) θ)
    (hwidth : ∀ x ∈ S, ∀ y ∈ S, |inner ℝ (x - y) θ| ≤ δ) :
    Metric.diam S ≤ dist aMinus aPlus + 2 * δ * (c / s) + δ := by
  have hcot : 0 ≤ c / s := div_nonneg hc hs.le
  have hgap : inner ℝ aPlus e - inner ℝ aMinus e ≤ dist aMinus aPlus := by
    have h := (le_abs_self (inner ℝ (aPlus - aMinus) e)).trans
      (abs_real_inner_le_norm (aPlus - aMinus) e)
    simpa [inner_sub_left, he, dist_eq_norm, norm_sub_rev] using h
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  have hxbr := euclideanCap_transverse_brackets θ e aMinus aPlus x δ c s hc hs
    (hplus x hx) (hminus x hx) (hdepthPlus x hx) (hdepthMinus x hx)
  have hybr := euclideanCap_transverse_brackets θ e aMinus aPlus y δ c s hc hs
    (hplus y hy) (hminus y hy) (hdepthPlus y hy) (hdepthMinus y hy)
  have hewidth : |inner ℝ (x - y) e| ≤ dist aMinus aPlus + 2 * δ * (c / s) := by
    rw [inner_sub_left, abs_le]
    constructor <;> linarith
  calc
    dist x y = ‖x - y‖ := dist_eq_norm _ _
    _ ≤ |inner ℝ (x - y) θ| + |inner ℝ (x - y) e| :=
      euclideanPlane_norm_le_orthogonal_coordinates θ e (x - y) hθ he horth
    _ ≤ δ + (dist aMinus aPlus + 2 * δ * (c / s)) :=
      add_le_add (hwidth x hx y hy) hewidth
    _ = _ := by ring

/-- The symmetric-angle form of the spatial cap estimate. The hypotheses
explicitly associate `aPlus` to the plus normal and `aMinus` to the minus normal. -/
theorem euclideanCap_diam_le_trigonometric
    (S : Set (EuclideanSpace ℝ (Fin 2)))
    (θ e aMinus aPlus : EuclideanSpace ℝ (Fin 2)) (δ η : ℝ)
    (hθ : ‖θ‖ = 1) (he : ‖e‖ = 1) (horth : inner ℝ θ e = 0)
    (hδ : 0 < δ) (hη : 0 < η) (hηhalf : η < Real.pi / 2)
    (hplus : ∀ z ∈ S,
      inner ℝ (z - aPlus) (Real.cos η • θ + Real.sin η • e) ≤ 0)
    (hminus : ∀ z ∈ S,
      inner ℝ (z - aMinus) (Real.cos η • θ - Real.sin η • e) ≤ 0)
    (hdepthPlus : ∀ z ∈ S, -δ ≤ inner ℝ (z - aPlus) θ)
    (hdepthMinus : ∀ z ∈ S, -δ ≤ inner ℝ (z - aMinus) θ)
    (hwidth : ∀ x ∈ S, ∀ y ∈ S, |inner ℝ (x - y) θ| ≤ δ) :
    Metric.diam S ≤ dist aMinus aPlus + 2 * δ * (Real.cos η / Real.sin η) + δ := by
  have hc : 0 ≤ Real.cos η := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hηhalf⟩).le
  have hs : 0 < Real.sin η := Real.sin_pos_of_pos_of_lt_pi hη
    (by linarith [Real.pi_pos])
  exact euclideanCap_diam_le S θ e aMinus aPlus δ (Real.cos η) (Real.sin η)
    hθ he horth hδ.le hc hs hplus hminus hdepthPlus hdepthMinus hwidth

end Markov
