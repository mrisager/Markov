import Markov.TraceUnresolvedSupportingPoints
import Markov.TraceConvexCap
import Markov.TraceCutoffSmallAngle
import Markov.CircleNormalOffsets
import Markov.TraceUnresolvedArcLength
import Markov.TraceUnresolvedMonotone
import Markov.TraceResolvedSupportingPoints

/-! Actual cap bounds for the constructed trace ball. Endpoint normal
association and finite curve-distance estimates are discharged in the
unresolved case, including for the concrete component variation in (83).
The geometric B_X identification is separate. -/

noncomputable section
open Set
open scoped Classical
namespace Markov

theorem norm_eq_one_of_mem_closure_trace_component
    (H : ℝ) (x y : TracePlane)
    (hy : y ∈ closure (connectedComponentIn (traceUncutBoundary H) x)) : ‖y‖ = 1 := by
  have hsub : connectedComponentIn (traceUncutBoundary H) x ⊆
      {p : TracePlane | ‖p‖ = 1} := by
    intro p hp
    have hp' := connectedComponentIn_subset (traceUncutBoundary H) x hp
    exact norm_eq_one_of_mem_traceUncutBoundary H p hp'
  exact closure_minimal hsub (isClosed_eq continuous_norm continuous_const) hy

/-- The actual unresolved cap is controlled by the variation of any
signed parametrization of that same associated component. -/
theorem traceConvexCap_unresolved_component_bound
    (H ε η δ : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength * H)))
    (z : EuclideanSpace ℝ (Fin 2)) (x : TracePlane) (hx : x ∈ traceUncutBoundary H)
    (hz : z ∈ closedAngularNeighborhood
      (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η)
    (k : Fin 8) (u v : ℤ × ℤ) (hcut : ConsecutiveCutoffSlopes ⌊H⌋₊ u v)
    (hcomp : connectedComponentIn (traceUncutBoundary H) x =
      slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v)) :
    Metric.diam (traceConvexCap z δ) ≤
      (signedTraceCutoffArcLength k u v).toReal + 2 * Real.pi * δ / η := by
  obtain ⟨α, xMinus, xPlus, hzeq, hMinus, hPlus, hnMinus, hnPlus⟩ :=
    trace_unresolved_component_supporting_points H ε η hH hε hη hbasic z x hx hz
  have hzunit : ‖z‖ = 1 := by rw [hzeq]; exact norm_circleNormal α
  have hxm := norm_eq_one_of_mem_closure_trace_component H x xMinus hMinus
  have hxp := norm_eq_one_of_mem_closure_trace_component H x xPlus hPlus
  have hdist : dist (traceEuclideanCoordinates xMinus) (traceEuclideanCoordinates xPlus) ≤
      (signedTraceCutoffArcLength k u v).toReal := by
    rw [hcomp] at hMinus hPlus
    exact dist_traceEuclideanCoordinates_le_signedTraceCutoffArcLength
      ⌊H⌋₊ k u v hcut xMinus xPlus hMinus hPlus
  have hsmall := trace_basic_angle_lt_pi_div_eight H ε η hH hε hη hbasic
  apply traceConvexCap_diam_le_of_dist_le z (quarterTurnNormal z) xMinus xPlus δ η _
    hzunit (by rw [norm_quarterTurnNormal, hzunit]) (inner_quarterTurnNormal_self z)
    hxm hxp hδ hη (by linarith [Real.pi_pos]) _ _ hdist
  · simpa only [circleNormal_sub_eq_offset, ← hzeq] using hnMinus
  · simpa only [circleNormal_add_eq_offset, ← hzeq] using hnPlus

/-- The unresolved cap bound uses exactly the same concrete finite
component variation as the proved weighted estimate (83). -/
theorem traceConvexCap_unresolved_covector_bound
    (K H ε η δ : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength * H)))
    (d : ℤ × ℤ) (hd : IsTraceUnresolved d K H η) :
    Metric.diam (traceConvexCap (NormedSpace.normalize (euclideanIntDirection d)) δ) ≤
      traceUnresolvedArcLength d K H η + 2 * Real.pi * δ / η := by
  obtain ⟨x, hx, k, u, v, hcut, hxcomp, hcomp, hmem, _, hlength⟩ :=
    traceUnresolvedArcLength_spec d K H η hd hH
  rw [← hxcomp] at hmem
  have h := traceConvexCap_unresolved_component_bound H ε η δ hH hε hη hδ hbasic
    (NormedSpace.normalize (euclideanIntDirection d)) x hx hmem k u v hcut
    (hxcomp.trans hcomp)
  simpa only [hlength] using h

theorem norm_eq_one_of_mem_real_traceCutoffCorners
    (H : ℝ) (x : TracePlane) (hx : x ∈ realCutoffCorners traceBasis H) : ‖x‖ = 1 := by
  obtain ⟨p, hp, _, rfl⟩ := hx
  exact NormedSpace.norm_normalize (norm_pos_iff.mp
    (traceAxisLength_pos.trans_le (traceAxisLength_le_norm_intVector p hp)))

/-- In the resolved case the two actual support points are the same
cutoff corner, so only the universal cap error remains. -/
theorem traceConvexCap_resolved_bound
    (H ε η δ : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength * H)))
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1)
    (hresolved : ¬ IsTraceUnresolvedNormal z H η) :
    Metric.diam (traceConvexCap z δ) ≤ 2 * Real.pi * δ / η := by
  obtain ⟨α, x, hzeq, hxcut, hnMinus, hnPlus⟩ :=
    trace_resolved_normal_exists_same_cutoff_support z H η hz hη.le hresolved
  have hx := norm_eq_one_of_mem_real_traceCutoffCorners H x hxcut
  have hsmall := trace_basic_angle_lt_pi_div_eight H ε η hH hε hη hbasic
  have hcap := traceConvexCap_diam_le z (quarterTurnNormal z) x x δ η
    hz (by rw [norm_quarterTurnNormal, hz]) (inner_quarterTurnNormal_self z)
    hx hx hδ hη (by linarith [Real.pi_pos])
    (by simpa only [circleNormal_sub_eq_offset, ← hzeq] using hnMinus)
    (by simpa only [circleNormal_add_eq_offset, ← hzeq] using hnPlus)
  simpa only [dist_self, zero_add] using hcap

/-- Both alternatives of v1 Lemma 8 hold for the actual constructed
trace ball. The unresolved arc size is its actual finite curve variation. -/
theorem trace_lemma8
    (H ε η δ : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength * H)))
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1) :
    (¬ IsTraceUnresolvedNormal z H η →
      Metric.diam (traceConvexCap z δ) ≤ 2 * Real.pi * δ / η) ∧
    (IsTraceUnresolvedNormal z H η →
      ∃ x ∈ traceUncutBoundary H, ∃ (k : Fin 8) (u v : ℤ × ℤ),
        ConsecutiveCutoffSlopes ⌊H⌋₊ u v ∧
        connectedComponentIn (traceUncutBoundary H) x =
          slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) ∧
        Metric.diam (traceConvexCap z δ) ≤
          (signedTraceCutoffArcLength k u v).toReal + 2 * Real.pi * δ / η) := by
  refine ⟨traceConvexCap_resolved_bound H ε η δ hH hε hη hδ hbasic z hz, ?_⟩
  rintro ⟨x, hx, hmem⟩
  obtain ⟨k, u, v, hcut, _, hcomp⟩ :=
    traceUncutBoundary_exists_signed_cutoff_component H hH x hx
  exact ⟨x, hx, k, u, v, hcut, hcomp,
    traceConvexCap_unresolved_component_bound H ε η δ hH hε hη hδ hbasic
      z x hx hmem k u v hcut hcomp⟩

/-- The cap estimate for an integral direction uses the exact same
component-size function as the actual weighted estimate (83). -/
theorem trace_lemma8_covector
    (K H ε η δ : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength * H)))
    (d : ℤ × ℤ) (hd : d ≠ (0, 0)) (hK : intEuclidean d ≤ K) :
    Metric.diam (traceConvexCap (NormedSpace.normalize (euclideanIntDirection d)) δ) ≤
      (if IsTraceUnresolved d K H η then traceUnresolvedArcLength d K H η else 0) +
        2 * Real.pi * δ / η := by
  classical
  by_cases hu : IsTraceUnresolved d K H η
  · rw [if_pos hu]
    exact traceConvexCap_unresolved_covector_bound K H ε η δ hH hε hη hδ hbasic d hu
  · rw [if_neg hu, zero_add]
    apply traceConvexCap_resolved_bound H ε η δ hH hε hη hδ hbasic _
      (NormedSpace.norm_normalize (euclideanIntDirection_ne_zero d hd))
    intro hn
    exact hu ((isTraceUnresolved_iff_normal d K H η).mpr ⟨hd, hK, hn⟩)

end Markov
