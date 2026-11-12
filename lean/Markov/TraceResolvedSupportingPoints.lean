import Markov.TraceSupportLocation
import Markov.TraceUnresolvedAngularWidth
import Markov.TraceUnresolvedMonotone

/-! A normal outside all enlarged uncut-component normal arcs lies
strictly inside a single actual cutoff corner fibre. Its two angular
offsets therefore have the same actual supporting corner. The incoming
and outgoing normals are obtained from adjacent uncut arcs, including
the seam between parameters four and zero. -/

noncomputable section
open Set

namespace Markov

/-- Only finitely many interior parameters of one traversal are removed
by any actual primitive-height cutoff. -/
theorem traceBoundary_cutoff_interior_parameters_finite (H : ℝ) :
    {t : ℝ | t ∈ Ioo (0 : ℝ) 4 ∧
      traceBoundaryPath t ∈ realCutoffCorners traceBasis H}.Finite := by
  apply Set.Finite.of_injOn (f := traceBoundaryPath)
    (fun t ht => ht.2) _ (realCutoffCorners_finite traceBasis H)
  intro s hs t ht heq
  exact traceBoundaryPath_injOn_Ioc ⟨hs.1.1, hs.1.2.le⟩
    ⟨ht.1.1, ht.1.2.le⟩ heq

/-- Near a given parameter there are no other removed parameters. -/
private theorem traceBoundary_exists_cutoff_free_interval (H t : ℝ) :
    ∃ a b : ℝ, a < t ∧ t < b ∧ ∀ s ∈ Ioo a b,
      s ∈ Ioo (0 : ℝ) 4 → s ≠ t →
      traceBoundaryPath s ∈ traceUncutBoundary H := by
  let C := {s : ℝ | s ∈ Ioo (0 : ℝ) 4 ∧
    traceBoundaryPath s ∈ realCutoffCorners traceBasis H}
  have hC : C.Finite := traceBoundary_cutoff_interior_parameters_finite H
  have hn : t ∉ C \ {t} := by simp
  have hneigh : (C \ {t})ᶜ ∈ nhds t := hC.diff.isClosed.compl_mem_nhds hn
  obtain ⟨a, b, ht, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hneigh
  refine ⟨a, b, ht.1, ht.2, ?_⟩
  intro s hs hsI hst
  refine ⟨traceBoundaryPath_mem_frontier s, ?_⟩
  intro hcut
  exact hab hs ⟨⟨hsI, hcut⟩, hst⟩

/-- A nonempty open path arc that avoids the cutoff is contained in one
actual uncut component. -/
private theorem traceBoundaryOpenArc_subset_uncut_component
    (H a b : ℝ) (hab : a < b)
    (huncut : traceBoundaryOpenArc a b ⊆ traceUncutBoundary H) :
    ∃ x ∈ traceUncutBoundary H,
      traceBoundaryOpenArc a b ⊆ connectedComponentIn (traceUncutBoundary H) x := by
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hx : traceBoundaryPath ((a + b) / 2) ∈ traceBoundaryOpenArc a b :=
    ⟨(a + b) / 2, hm, rfl⟩
  refine ⟨traceBoundaryPath ((a + b) / 2), huncut hx, ?_⟩
  exact (isPreconnected_Ioo.image traceBoundaryPath
    continuous_traceBoundaryPath.continuousOn).subset_connectedComponentIn hx huncut

/-- The outgoing normal at any parameter before the terminal seam is a
limit normal of the actual uncut component immediately to its right. -/
theorem traceBoundary_outgoing_normal_mem_uncut_closure
    (H t : ℝ) (ht : t ∈ Ico (0 : ℝ) 4) :
    ∃ x ∈ traceUncutBoundary H,
      circleNormal (traceCyclicAngleLift t) ∈ closure
        (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) := by
  obtain ⟨a, b, hat, htb, hfree⟩ := traceBoundary_exists_cutoff_free_interval H t
  let r := min b 4
  have htr : t < r := lt_min htb ht.2
  have huncut : traceBoundaryOpenArc t r ⊆ traceUncutBoundary H := by
    rintro y ⟨s, hs, rfl⟩
    apply hfree s ⟨hat.trans hs.1, hs.2.trans_le (min_le_left _ _)⟩
      ⟨ht.1.trans_lt hs.1, hs.2.trans_le (min_le_right _ _)⟩
    exact ne_of_gt hs.1
  obtain ⟨x, hx, hsub⟩ := traceBoundaryOpenArc_subset_uncut_component H t r htr huncut
  refine ⟨x, hx, closure_mono (normalsOn_mono traceBasis hsub) ?_⟩
  rw [closure_normalsOn_traceBoundaryOpenArc t r ht.1 htr (min_le_right _ _)]
  exact ⟨traceCyclicAngleLift t,
    ⟨le_rfl, traceCyclicAngleLift.mono.le_leftLim htr⟩, rfl⟩

/-- The incoming normal at any positive parameter is a limit normal of
the actual uncut component immediately to its left. -/
theorem traceBoundary_incoming_normal_mem_uncut_closure
    (H t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 4) :
    ∃ x ∈ traceUncutBoundary H,
      circleNormal (Function.leftLim traceCyclicAngleLift t) ∈ closure
        (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) := by
  obtain ⟨a, b, hat, htb, hfree⟩ := traceBoundary_exists_cutoff_free_interval H t
  let l := max a 0
  have hlt : l < t := max_lt hat ht.1
  have huncut : traceBoundaryOpenArc l t ⊆ traceUncutBoundary H := by
    rintro y ⟨s, hs, rfl⟩
    apply hfree s ⟨(le_max_left _ _).trans_lt hs.1, hs.2.trans htb⟩
      ⟨(le_max_right _ _).trans_lt hs.1, hs.2.trans_le ht.2⟩
    exact ne_of_lt hs.2
  obtain ⟨x, hx, hsub⟩ := traceBoundaryOpenArc_subset_uncut_component H l t hlt huncut
  refine ⟨x, hx, closure_mono (normalsOn_mono traceBasis hsub) ?_⟩
  rw [closure_normalsOn_traceBoundaryOpenArc l t (le_max_right _ _) hlt ht.2]
  exact ⟨Function.leftLim traceCyclicAngleLift t,
    ⟨traceCyclicAngleLift.mono.le_leftLim hlt, le_rfl⟩, rfl⟩

/-- The outgoing seam normal is supplied by the component just after
parameter zero, using only the actual increment from zero to four. -/
theorem traceBoundary_outgoing_normal_mem_uncut_closure_Ioc
    (H t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 4) :
    ∃ x ∈ traceUncutBoundary H,
      circleNormal (traceCyclicAngleLift t) ∈ closure
        (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) := by
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · exact traceBoundary_outgoing_normal_mem_uncut_closure H t ⟨ht.1.le, hlt⟩
  · obtain ⟨x, hx, hn⟩ := traceBoundary_outgoing_normal_mem_uncut_closure H 0
      (by constructor <;> norm_num)
    refine ⟨x, hx, ?_⟩
    have hF : traceCyclicAngleLift 4 = traceCyclicAngleLift 0 + 2 * Real.pi := by
      linarith [traceCyclicAngleLift_period_increment]
    simpa only [hF, circleNormal_add_two_pi] using hn

/-- A nearby closure normal on one actual uncut component witnesses the
original unresolved-normal condition with the exact angular radius. -/
theorem isTraceUnresolvedNormal_of_mem_normal_closure
    (H η : ℝ) (z y : EuclideanSpace ℝ (Fin 2)) (x : TracePlane)
    (hx : x ∈ traceUncutBoundary H) (hz : ‖z‖ = 1)
    (hy : y ∈ closure
      (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)))
    (hangle : InnerProductGeometry.angle y z ≤ η) :
    IsTraceUnresolvedNormal z H η := by
  refine ⟨x, hx, ?_⟩
  exact (mem_closedAngularNeighborhood_iff_exists_mem_closure _
    (traceUncutBoundary_component_normals_nonempty H x hx)
    (traceUncutBoundary_component_normals_unit H x) z η).mpr ⟨hz, y, hy, hangle⟩

/-- A genuine support point of a resolved normal must be one of the
actual removed corners. -/
theorem trace_support_point_mem_cutoff_of_not_unresolved
    (H η : ℝ) (hη : 0 ≤ η) (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1)
    (hresolved : ¬ IsTraceUnresolvedNormal z H η)
    (x : TracePlane) (hx : x ∈ frontier (Metric.closedBall (0 : TracePlane) 1))
    (hn : z ∈ normalsOn traceBasis {x}) : x ∈ realCutoffCorners traceBasis H := by
  by_contra hcut
  have hxuncut : x ∈ traceUncutBoundary H := ⟨hx, hcut⟩
  have hsub : ({x} : Set TracePlane) ⊆
      connectedComponentIn (traceUncutBoundary H) x := by
    intro y hy
    rcases hy with rfl
    exact mem_connectedComponentIn hxuncut
  have hzne : z ≠ 0 := by intro hzero; simp [hzero] at hz
  exact hresolved (isTraceUnresolvedNormal_of_mem_normal_closure H η z z x
    hxuncut hz (subset_closure (normalsOn_mono traceBasis hsub hn))
    (by simpa only [InnerProductGeometry.angle_self hzne] using hη))

/-- Every unit normal has a supporting parameter in the single half-open
traversal; the initial point is represented by parameter four. -/
theorem traceBoundary_support_exists_Ioc_of_unit_normal
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1) :
    ∃ t ∈ Ioc (0 : ℝ) 4, z ∈ normalsOn traceBasis {traceBoundaryPath t} := by
  obtain ⟨t, ht, hn⟩ := traceBoundary_support_exists_of_unit_normal z hz
  by_cases ht0 : t = 0
  · subst t
    exact ⟨4, by constructor <;> norm_num,
      by simpa only [traceBoundaryPath_four_eq_zero] using hn⟩
  · exact ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩, hn⟩

/-- Outside all enlarged uncut-component normal arcs, both angular
offsets are genuine support normals at the same actual cutoff corner. -/
theorem trace_resolved_normal_exists_same_cutoff_support
    (z : EuclideanSpace ℝ (Fin 2)) (H η : ℝ) (hz : ‖z‖ = 1) (hη : 0 ≤ η)
    (hresolved : ¬ IsTraceUnresolvedNormal z H η) :
    ∃ (α : ℝ) (x : TracePlane), z = circleNormal α ∧
      x ∈ realCutoffCorners traceBasis H ∧
      circleNormal (α - η) ∈ normalsOn traceBasis {x} ∧
      circleNormal (α + η) ∈ normalsOn traceBasis {x} := by
  obtain ⟨t, ht, hn⟩ := traceBoundary_support_exists_Ioc_of_unit_normal z hz
  have hcut := trace_support_point_mem_cutoff_of_not_unresolved H η hη z hz
    hresolved (traceBoundaryPath t) (traceBoundaryPath_mem_frontier t) hn
  rw [traceBoundaryPath_normals_eq_lift_arc t ht] at hn
  obtain ⟨α, hα, hαz⟩ := hn
  have hleft : η < α - Function.leftLim traceCyclicAngleLift t := by
    by_contra h
    obtain ⟨x, hx, hclosure⟩ := traceBoundary_incoming_normal_mem_uncut_closure H t ht
    apply hresolved (isTraceUnresolvedNormal_of_mem_normal_closure H η z
      (circleNormal (Function.leftLim traceCyclicAngleLift t)) x hx hz hclosure ?_)
    rw [← hαz]
    apply (angle_circleNormal_le_abs_sub _ _).trans
    rw [abs_of_nonpos (sub_nonpos.mpr hα.1)]
    linarith
  have hright : η < traceCyclicAngleLift t - α := by
    by_contra h
    obtain ⟨x, hx, hclosure⟩ := traceBoundary_outgoing_normal_mem_uncut_closure_Ioc H t ht
    apply hresolved (isTraceUnresolvedNormal_of_mem_normal_closure H η z
      (circleNormal (traceCyclicAngleLift t)) x hx hz hclosure ?_)
    rw [← hαz]
    apply (angle_circleNormal_le_abs_sub _ _).trans
    rw [abs_of_nonneg (sub_nonneg.mpr hα.2)]
    linarith
  refine ⟨α, traceBoundaryPath t, hαz.symm, hcut, ?_, ?_⟩
  · rw [traceBoundaryPath_normals_eq_lift_arc t ht]
    exact ⟨α - η, ⟨by linarith, by linarith [hα.2]⟩, rfl⟩
  · rw [traceBoundaryPath_normals_eq_lift_arc t ht]
    exact ⟨α + η, ⟨by linarith [hα.1], by linarith⟩, rfl⟩

end Markov
