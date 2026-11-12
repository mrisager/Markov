import Markov.TraceLatticeCount
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! A concrete radial mollifier for the fixed Euclidean plane.
The explicit inner-product bump base is used so that radiality follows from
its formula, without assigning radiality to an arbitrary chosen bump base. -/

noncomputable section
open Set MeasureTheory Function
open scoped Topology ContDiff
namespace Markov

/-- The explicit radial smooth bump, equal to one on radius `1/2` and
supported in the open unit ball. -/
def traceRadialBump (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace (EuclideanSpace ℝ (Fin 2))).toFun 2 ((2 : ℝ) • x)

theorem traceRadialBump_nonneg (x : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ traceRadialBump x :=
  ((ContDiffBumpBase.ofInnerProductSpace (EuclideanSpace ℝ (Fin 2))).mem_Icc 2 ((2 : ℝ) • x)).1

theorem traceRadialBump_contDiff : ContDiff ℝ ∞ traceRadialBump := by
  have hc : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 2) =>
      ((2 : ℝ), (2 : ℝ) • x)) := by fun_prop
  exact (ContDiffBumpBase.ofInnerProductSpace (EuclideanSpace ℝ (Fin 2))).smooth.comp_contDiff
    hc
    (fun _ => ⟨by norm_num, mem_univ _⟩)

theorem traceRadialBump_radial (x y : EuclideanSpace ℝ (Fin 2)) (h : ‖x‖ = ‖y‖) :
    traceRadialBump x = traceRadialBump y := by
  simp [traceRadialBump, ContDiffBumpBase.ofInnerProductSpace, norm_smul, h]

theorem traceRadialBump_support_eq :
    support traceRadialBump = Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  ext x
  change ((2 : ℝ) • x) ∈ support
    ((ContDiffBumpBase.ofInnerProductSpace (EuclideanSpace ℝ (Fin 2))).toFun 2) ↔ _
  rw [(ContDiffBumpBase.ofInnerProductSpace (EuclideanSpace ℝ (Fin 2))).support 2
    (by norm_num)]
  simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
  norm_num

theorem traceRadialBump_hasCompactSupport : HasCompactSupport traceRadialBump := by
  rw [HasCompactSupport, tsupport, traceRadialBump_support_eq,
    closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
  exact isCompact_closedBall _ _

theorem traceRadialBump_integrable : Integrable traceRadialBump :=
  traceRadialBump_contDiff.continuous.integrable_of_hasCompactSupport
    traceRadialBump_hasCompactSupport

theorem traceRadialBump_integral_pos : 0 < ∫ x, traceRadialBump x := by
  apply (integral_pos_iff_support_of_nonneg traceRadialBump_nonneg
    traceRadialBump_integrable).mpr
  rw [traceRadialBump_support_eq]
  exact Metric.measure_ball_pos volume _ (by norm_num)

/-- The explicit radial bump normalized by its positive Euclidean integral. -/
def traceRadialMollifier (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  traceRadialBump x / ∫ y, traceRadialBump y

theorem traceRadialMollifier_nonneg (x : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ traceRadialMollifier x :=
  div_nonneg (traceRadialBump_nonneg x) traceRadialBump_integral_pos.le

theorem traceRadialMollifier_contDiff : ContDiff ℝ ∞ traceRadialMollifier :=
  traceRadialBump_contDiff.div_const _

theorem traceRadialMollifier_radial (x y : EuclideanSpace ℝ (Fin 2)) (h : ‖x‖ = ‖y‖) :
    traceRadialMollifier x = traceRadialMollifier y := by
  rw [traceRadialMollifier, traceRadialMollifier, traceRadialBump_radial x y h]

theorem traceRadialMollifier_support_eq :
    support traceRadialMollifier = Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  unfold traceRadialMollifier
  rw [support_div, traceRadialBump_support_eq,
    support_const traceRadialBump_integral_pos.ne', inter_univ]

theorem traceRadialMollifier_tsupport_eq :
    tsupport traceRadialMollifier = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  rw [tsupport, traceRadialMollifier_support_eq, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]

theorem traceRadialMollifier_hasCompactSupport : HasCompactSupport traceRadialMollifier := by
  rw [HasCompactSupport, traceRadialMollifier_tsupport_eq]
  exact isCompact_closedBall _ _

theorem traceRadialMollifier_integrable : Integrable traceRadialMollifier :=
  traceRadialBump_integrable.div_const _

theorem traceRadialMollifier_integral : ∫ x, traceRadialMollifier x = 1 := by
  change (∫ x, traceRadialBump x / ∫ y, traceRadialBump y) = 1
  rw [integral_div]
  exact div_self traceRadialBump_integral_pos.ne'

theorem traceRadialMollifier_eq_zero_of_one_le_norm (x : EuclideanSpace ℝ (Fin 2))
    (hx : 1 ≤ ‖x‖) : traceRadialMollifier x = 0 := by
  apply notMem_support.mp
  rw [traceRadialMollifier_support_eq]
  simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hx

/-- The two-dimensional dilation `ρ_Q(x) = Q² ρ(Qx)`. -/
def traceScaledMollifier (Q : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Q ^ 2 * traceRadialMollifier (Q • x)

theorem traceScaledMollifier_nonneg (Q : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ traceScaledMollifier Q x :=
  mul_nonneg (sq_nonneg Q) (traceRadialMollifier_nonneg _)

theorem traceScaledMollifier_contDiff (Q : ℝ) :
    ContDiff ℝ ∞ (traceScaledMollifier Q) := by
  have hc : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 2) => Q • x) := by fun_prop
  exact contDiff_const.mul (traceRadialMollifier_contDiff.comp hc)

theorem traceScaledMollifier_radial (Q : ℝ) (x y : EuclideanSpace ℝ (Fin 2))
    (h : ‖x‖ = ‖y‖) : traceScaledMollifier Q x = traceScaledMollifier Q y := by
  unfold traceScaledMollifier
  rw [traceRadialMollifier_radial (Q • x) (Q • y) (by simp only [norm_smul, h])]

theorem traceScaledMollifier_eq_zero_of_inv_le_norm (Q : ℝ) (hQ : 0 < Q)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : Q⁻¹ ≤ ‖x‖) : traceScaledMollifier Q x = 0 := by
  unfold traceScaledMollifier
  rw [traceRadialMollifier_eq_zero_of_one_le_norm]
  · exact mul_zero _
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hQ]
    calc
      1 = Q * Q⁻¹ := (mul_inv_cancel₀ hQ.ne').symm
      _ ≤ Q * ‖x‖ := mul_le_mul_of_nonneg_left hx hQ.le

theorem traceScaledMollifier_integral (Q : ℝ) (hQ : 0 < Q) :
    ∫ x, traceScaledMollifier Q x = 1 := by
  change (∫ x : EuclideanSpace ℝ (Fin 2), Q ^ 2 * traceRadialMollifier (Q • x)) = 1
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume traceRadialMollifier Q (hR := hQ.le)]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, traceRadialMollifier_integral, mul_one]
  exact mul_inv_cancel₀ (pow_ne_zero _ hQ.ne')

theorem traceScaledMollifier_support_eq (Q : ℝ) (hQ : 0 < Q) :
    support (traceScaledMollifier Q) =
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) Q⁻¹ := by
  ext x
  have hn : Q ^ 2 ≠ 0 := pow_ne_zero _ hQ.ne'
  change Q ^ 2 * traceRadialMollifier (Q • x) ≠ 0 ↔ _
  rw [mul_ne_zero_iff, and_iff_right hn]
  change (Q • x) ∈ support traceRadialMollifier ↔ _
  rw [traceRadialMollifier_support_eq]
  simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hQ]
  constructor
  · intro hx
    have hh := mul_lt_mul_of_pos_left hx (inv_pos.mpr hQ)
    simpa only [← mul_assoc, inv_mul_cancel₀ hQ.ne', one_mul, mul_one] using hh
  · intro hx
    calc
      Q * ‖x‖ < Q * Q⁻¹ := mul_lt_mul_of_pos_left hx hQ
      _ = 1 := mul_inv_cancel₀ hQ.ne'

theorem traceScaledMollifier_tsupport_eq (Q : ℝ) (hQ : 0 < Q) :
    tsupport (traceScaledMollifier Q) =
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) Q⁻¹ := by
  rw [tsupport, traceScaledMollifier_support_eq Q hQ,
    closure_ball _ (inv_ne_zero hQ.ne')]

theorem traceScaledMollifier_hasCompactSupport (Q : ℝ) (hQ : 0 < Q) :
    HasCompactSupport (traceScaledMollifier Q) := by
  rw [HasCompactSupport, traceScaledMollifier_tsupport_eq Q hQ]
  exact isCompact_closedBall _ _

theorem traceScaledMollifier_integrable (Q : ℝ) (hQ : 0 < Q) :
    Integrable (traceScaledMollifier Q) :=
  (traceScaledMollifier_contDiff Q).continuous.integrable_of_hasCompactSupport
    (traceScaledMollifier_hasCompactSupport Q hQ)

end Markov
