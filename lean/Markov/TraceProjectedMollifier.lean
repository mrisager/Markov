import Markov.TraceRadialMollifier
import Markov.OrientedPlaneCoordinates

/-! The one-dimensional projection of the actual radial smoothing kernel.
It is continuous, compactly supported, nonnegative, integrable, and has mass
one with respect to standard one-dimensional Lebesgue measure. -/

noncomputable section
open Set MeasureTheory Function
open scoped Topology
namespace Markov

/-- Projection of the radial plane mollifier onto a normal coordinate. -/
def traceProjectedMollifier (Q : ℝ) (θ : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : ℝ :=
  ∫ s : ℝ, traceScaledMollifier Q (t • θ + s • quarterTurnNormal θ)

theorem traceProjectedMollifier_nonneg (Q : ℝ) (θ : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    0 ≤ traceProjectedMollifier Q θ t :=
  integral_nonneg (fun _ => traceScaledMollifier_nonneg Q _)

theorem traceScaledMollifier_oriented_eq_zero_of_inv_le_abs_normal
    (Q : ℝ) (hQ : 0 < Q) (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1)
    (t s : ℝ) (ht : Q⁻¹ ≤ |t|) :
    traceScaledMollifier Q (t • θ + s • quarterTurnNormal θ) = 0 := by
  have hn : |t| ≤ ‖orientedPlaneCoordinates θ hθ (t, s)‖ := by
    simpa only [orientedPlaneCoordinates_inner_normal, hθ, mul_one] using
      abs_real_inner_le_norm (orientedPlaneCoordinates θ hθ (t, s)) θ
  apply traceScaledMollifier_eq_zero_of_inv_le_norm Q hQ
  simpa only [orientedPlaneCoordinates_apply] using ht.trans hn

theorem traceScaledMollifier_oriented_eq_zero_of_inv_le_abs_transverse
    (Q : ℝ) (hQ : 0 < Q) (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1)
    (t s : ℝ) (hs : Q⁻¹ ≤ |s|) :
    traceScaledMollifier Q (t • θ + s • quarterTurnNormal θ) = 0 := by
  have hn : |s| ≤ ‖orientedPlaneCoordinates θ hθ (t, s)‖ := by
    simpa only [orientedPlaneCoordinates_inner_transverse, norm_quarterTurnNormal,
      hθ, mul_one] using
      abs_real_inner_le_norm (orientedPlaneCoordinates θ hθ (t, s)) (quarterTurnNormal θ)
  apply traceScaledMollifier_eq_zero_of_inv_le_norm Q hQ
  simpa only [orientedPlaneCoordinates_apply] using hs.trans hn

theorem traceProjectedMollifier_eq_zero_of_inv_le_abs
    (Q : ℝ) (hQ : 0 < Q) (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1)
    (t : ℝ) (ht : Q⁻¹ ≤ |t|) : traceProjectedMollifier Q θ t = 0 := by
  unfold traceProjectedMollifier
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall (fun s =>
    traceScaledMollifier_oriented_eq_zero_of_inv_le_abs_normal Q hQ θ hθ t s ht)

theorem traceProjectedMollifier_support_subset
    (Q : ℝ) (hQ : 0 < Q) (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1) :
    support (traceProjectedMollifier Q θ) ⊆ Ioo (-Q⁻¹) Q⁻¹ := by
  intro t ht
  apply abs_lt.mp
  apply lt_of_not_ge
  intro hh
  exact ht (traceProjectedMollifier_eq_zero_of_inv_le_abs Q hQ θ hθ t hh)

theorem traceProjectedMollifier_tsupport_subset
    (Q : ℝ) (hQ : 0 < Q) (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1) :
    tsupport (traceProjectedMollifier Q θ) ⊆ Icc (-Q⁻¹) Q⁻¹ := by
  apply closure_minimal _ isClosed_Icc
  exact (traceProjectedMollifier_support_subset Q hQ θ hθ).trans Ioo_subset_Icc_self

theorem traceProjectedMollifier_hasCompactSupport
    (Q : ℝ) (hQ : 0 < Q) (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1) :
    HasCompactSupport (traceProjectedMollifier Q θ) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (traceProjectedMollifier_tsupport_subset Q hQ θ hθ)

theorem traceProjectedMollifier_continuous
    (Q : ℝ) (hQ : 0 < Q) (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1) :
    Continuous (traceProjectedMollifier Q θ) := by
  unfold traceProjectedMollifier
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (isCompact_Icc (a := -Q⁻¹) (b := Q⁻¹))
  · have hc := (traceScaledMollifier_contDiff Q).continuous.comp
      (orientedPlaneCoordinates_continuous θ hθ)
    simpa only [Function.comp_def, orientedPlaneCoordinates_apply] using hc.continuousOn
  · intro t s _ hs
    have hh : Q⁻¹ ≤ |s| := le_of_lt (lt_of_not_ge (fun hh => hs (abs_le.mp hh)))
    exact traceScaledMollifier_oriented_eq_zero_of_inv_le_abs_transverse Q hQ θ hθ t s hh

theorem traceScaledMollifier_oriented_integrable
    (Q : ℝ) (hQ : 0 < Q) (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1) :
    Integrable (fun p : ℝ × ℝ =>
      traceScaledMollifier Q (p.1 • θ + p.2 • quarterTurnNormal θ)) := by
  have hi := ((orientedPlaneCoordinates_measurePreserving θ hθ).integrable_comp_emb
    (orientedPlaneCoordinates θ hθ).measurableEmbedding).mpr
      (traceScaledMollifier_integrable Q hQ)
  simpa only [Function.comp_def, orientedPlaneCoordinates_apply] using hi

theorem traceProjectedMollifier_integrable
    (Q : ℝ) (hQ : 0 < Q) (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1) :
    Integrable (traceProjectedMollifier Q θ) :=
  (traceScaledMollifier_oriented_integrable Q hQ θ hθ).integral_prod_left

theorem traceProjectedMollifier_integral
    (Q : ℝ) (hQ : 0 < Q) (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1) :
    ∫ t : ℝ, traceProjectedMollifier Q θ t = 1 := by
  have hi := integral_orientedPlaneCoordinates_double θ hθ (traceScaledMollifier Q)
    (traceScaledMollifier_integrable Q hQ)
  rw [traceScaledMollifier_integral Q hQ] at hi
  exact hi.symm

end Markov
