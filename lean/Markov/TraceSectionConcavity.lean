import Markov.TraceSections
import Markov.OrientedPlaneCoordinates
import Mathlib.Analysis.Convex.Continuous

/-! Concavity and continuity of the actual perpendicular section profile. -/

noncomputable section
open Set Filter
open scoped Topology

namespace Markov

/-- The attained projection interval is exactly the range in which actual
transverse sections are nonempty. -/
theorem traceSection_nonempty_of_mem_support {θ : EuclideanSpace ℝ (Fin 2)}
    (hθ : ‖θ‖ = 1) {t : ℝ}
    (ht : t ∈ Icc (-traceEuclideanSupportHeight (-θ)) (traceEuclideanSupportHeight θ)) :
    (traceSection θ t).Nonempty := by
  let g : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := innerSL ℝ θ
  have hg (x : EuclideanSpace ℝ (Fin 2)) : g x = inner ℝ x θ := real_inner_comm x θ
  have hc : Convex ℝ (g '' traceEuclideanBall) :=
    strictConvex_traceEuclideanBall.convex.linear_image g.toLinearMap
  obtain ⟨p, hp, hpmax⟩ := traceEuclideanSupportHeight_exists_mem θ
  obtain ⟨q, hq, hqmax⟩ := traceEuclideanSupportHeight_exists_mem (-θ)
  have hpimg : traceEuclideanSupportHeight θ ∈ g '' traceEuclideanBall :=
    ⟨p, hp, (hg p).trans hpmax⟩
  have hqimg : -traceEuclideanSupportHeight (-θ) ∈ g '' traceEuclideanBall := by
    refine ⟨q, hq, ?_⟩
    rw [hg]
    rw [inner_neg_right] at hqmax
    linarith
  obtain ⟨x, hx, hxt⟩ := hc.ordConnected.out hqimg hpimg ht
  have hxt' : inner ℝ x θ = t := by simpa only [hg] using hxt
  have hrec : traceSectionPoint θ (inner ℝ x θ) (inner ℝ x (quarterTurnNormal θ)) = x := by
    have key := (orientedPlaneCoordinates θ hθ).apply_symm_apply x
    rw [orientedPlaneCoordinates_symm_apply, orientedPlaneCoordinates_apply] at key
    exact key
  refine ⟨inner ℝ x (quarterTurnNormal θ), ?_⟩
  change traceSectionPoint θ t (inner ℝ x (quarterTurnNormal θ)) ∈ traceEuclideanBall
  rw [← hxt', hrec]
  exact hx

/-- Convex combinations of points in two actual sections lie in the
corresponding intermediate section. -/
theorem traceSection_convex_combination (θ : EuclideanSpace ℝ (Fin 2))
    {a b s r u v : ℝ} (hs : s ∈ traceSection θ a) (hr : r ∈ traceSection θ b)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    u * s + v * r ∈ traceSection θ (u * a + v * b) := by
  have key := strictConvex_traceEuclideanBall.convex hs hr hu hv huv
  change traceSectionPoint θ (u * a + v * b) (u * s + v * r) ∈ traceEuclideanBall
  have hid : traceSectionPoint θ (u * a + v * b) (u * s + v * r) =
      u • traceSectionPoint θ a s + v • traceSectionPoint θ b r := by
    dsimp [traceSectionPoint]
    module
  rw [hid]
  exact key

/-- Lengths of actual parallel sections of the trace body form a concave
function on the body's exact projection interval. -/
theorem concaveOn_traceSectionProfile {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) :
    ConcaveOn ℝ (Icc (-traceEuclideanSupportHeight (-θ)) (traceEuclideanSupportHeight θ))
      (traceSectionProfile θ) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro a ha b hb u v hu hv huv
  have hane := traceSection_nonempty_of_mem_support hθ ha
  have hbne := traceSection_nonempty_of_mem_support hθ hb
  have hcne := traceSection_nonempty_of_mem_support hθ
    ((convex_Icc (-traceEuclideanSupportHeight (-θ)) (traceEuclideanSupportHeight θ))
      ha hb hu hv huv)
  have hca := isCompact_traceSection hθ a
  have hcb := isCompact_traceSection hθ b
  have hcc := isCompact_traceSection hθ (u * a + v * b)
  have hmin := traceSection_convex_combination θ (hca.sInf_mem hane) (hcb.sInf_mem hbne)
    hu hv huv
  have hmax := traceSection_convex_combination θ (hca.sSup_mem hane) (hcb.sSup_mem hbne)
    hu hv huv
  have hlo := csInf_le hcc.bddBelow hmin
  have hhi := le_csSup hcc.bddAbove hmax
  simp only [smul_eq_mul] at hcne ⊢
  rw [traceSectionProfile_eq_length hθ a hane,
    traceSectionProfile_eq_length hθ b hbne,
    traceSectionProfile_eq_length hθ (u * a + v * b) hcne]
  linarith

/-- The actual profile is continuous on the interior projection interval by concavity. -/
theorem continuousOn_traceSectionProfile_interior {θ : EuclideanSpace ℝ (Fin 2)}
    (hθ : ‖θ‖ = 1) :
    ContinuousOn (traceSectionProfile θ)
      (Ioo (-traceEuclideanSupportHeight (-θ)) (traceEuclideanSupportHeight θ)) := by
  simpa only [interior_Icc] using (concaveOn_traceSectionProfile hθ).continuousOn_interior

/-- Combining interior concavity, actual endpoint cap limits, and vanishing
outside the projection interval gives a continuous profile on the whole real line. -/
theorem continuous_traceSectionProfile {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) :
    Continuous (traceSectionProfile θ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases hlo : t = -traceEuclideanSupportHeight (-θ)
  · subst t
    exact (traceSectionProfile_continuousAt_support_endpoints hθ).2
  by_cases hhi : t = traceEuclideanSupportHeight θ
  · subst t
    exact (traceSectionProfile_continuousAt_support_endpoints hθ).1
  by_cases htlo : t < -traceEuclideanSupportHeight (-θ)
  · apply Filter.EventuallyEq.continuousAt (y := (0 : ℝ))
    filter_upwards [eventually_lt_nhds htlo] with s hs
    exact traceSectionProfile_eq_zero_of_outside_support hθ
      (fun hm ↦ (not_lt_of_ge hm.1) hs)
  by_cases hthi : traceEuclideanSupportHeight θ < t
  · apply Filter.EventuallyEq.continuousAt (y := (0 : ℝ))
    filter_upwards [eventually_gt_nhds hthi] with s hs
    exact traceSectionProfile_eq_zero_of_outside_support hθ
      (fun hm ↦ (not_lt_of_ge hm.2) hs)
  have ht : t ∈ Ioo (-traceEuclideanSupportHeight (-θ)) (traceEuclideanSupportHeight θ) :=
    ⟨lt_of_le_of_ne (le_of_not_gt htlo) (Ne.symm hlo),
      lt_of_le_of_ne (le_of_not_gt hthi) hhi⟩
  exact (continuousOn_traceSectionProfile_interior hθ).continuousAt (isOpen_Ioo.mem_nhds ht)

end Markov
