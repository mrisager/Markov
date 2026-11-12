import Markov.CompletedGraphInverse
import Markov.CircleAngularLift
import Markov.TraceClosedBoundaryArcs

/-! Actual supporting points from lifted normal angles, including the
initial corner. Only one traversal of the clamped angle lift is used.
The incoming angle at parameter zero comes from parameter four. -/

noncomputable section
open Set
namespace Markov

/-- The original normal-neighborhood condition, without restricting the
unit normal to an integral covector direction or imposing a size bound. -/
def IsTraceUnresolvedNormal (z : EuclideanSpace ℝ (Fin 2)) (H η : ℝ) : Prop :=
  ∃ x ∈ traceUncutBoundary H, z ∈ closedAngularNeighborhood
    (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η

theorem isTraceUnresolved_iff_normal (d : ℤ × ℤ) (K H η : ℝ) :
    IsTraceUnresolved d K H η ↔ d ≠ (0, 0) ∧ intEuclidean d ≤ K ∧
      IsTraceUnresolvedNormal (NormedSpace.normalize (euclideanIntDirection d)) H η := Iff.rfl

theorem circleNormal_add_two_pi (φ : ℝ) :
    circleNormal (φ + 2 * Real.pi) = circleNormal φ := by
  ext i
  fin_cases i <;> simp [circleNormal, Real.cos_add, Real.sin_add]

/-- The actual incoming angle at the initial seam is transported from
the terminal corner; it is not the left limit of the clamped lift at zero. -/
def traceBoundaryIncomingAngle (t : ℝ) : ℝ :=
  if t = 0 then Function.leftLim traceCyclicAngleLift 4 - 2 * Real.pi
  else Function.leftLim traceCyclicAngleLift t

theorem traceBoundaryIncomingAngle_le (t : ℝ) :
    traceBoundaryIncomingAngle t ≤ traceCyclicAngleLift t := by
  unfold traceBoundaryIncomingAngle
  split_ifs with ht
  · subst t
    have hl := traceCyclicAngleLift.mono.leftLim_le (le_refl (4 : ℝ))
    linarith [traceCyclicAngleLift_period_increment]
  · exact traceCyclicAngleLift.mono.leftLim_le le_rfl

/-- Every angle in the complete initial-corner fibre is a genuine
normal at the initial boundary point. -/
theorem traceBoundaryPath_zero_normal_of_angle_mem (φ : ℝ)
    (hφ : φ ∈ Icc (traceBoundaryIncomingAngle 0) (traceCyclicAngleLift 0)) :
    circleNormal φ ∈ normalsOn traceBasis {traceBoundaryPath 0} := by
  have hφ0 : Function.leftLim traceCyclicAngleLift 4 - 2 * Real.pi ≤ φ := by
    simpa only [traceBoundaryIncomingAngle, if_pos rfl] using hφ.1
  have hφ4 : φ + 2 * Real.pi ∈
      Icc (Function.leftLim traceCyclicAngleLift 4) (traceCyclicAngleLift 4) := by
    constructor <;> linarith [hφ.2, traceCyclicAngleLift_period_increment]
  have hm : circleNormal (φ + 2 * Real.pi) ∈
      normalsOn traceBasis {traceBoundaryPath 4} := by
    rw [traceBoundaryPath_normals_eq_lift_arc 4 (by norm_num)]
    exact ⟨φ + 2 * Real.pi, hφ4, rfl⟩
  simpa only [circleNormal_add_two_pi, traceBoundaryPath_four_eq_zero] using hm

/-- The completed normal graph supplies an actual supporting point in
the closed path arc, including the wrapped incoming fibre at parameter zero. -/
theorem traceBoundary_closedArc_support_exists
    (a b φ : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 4)
    (hφ : φ ∈ Icc (traceBoundaryIncomingAngle a) (traceCyclicAngleLift b)) :
    ∃ t ∈ Icc a b,
      circleNormal φ ∈ normalsOn traceBasis {traceBoundaryPath t} := by
  by_cases ha0 : a = 0
  · subst a
    by_cases hleft : φ ≤ traceCyclicAngleLift 0
    · exact ⟨0, ⟨le_rfl, hab.le⟩,
        traceBoundaryPath_zero_normal_of_angle_mem φ ⟨hφ.1, hleft⟩⟩
    by_cases hright : Function.leftLim traceCyclicAngleLift b ≤ φ
    · refine ⟨b, ⟨hab.le, le_rfl⟩, ?_⟩
      rw [traceBoundaryPath_normals_eq_lift_arc b ⟨hab, hb⟩]
      exact ⟨φ, ⟨hright, hφ.2⟩, rfl⟩
    obtain ⟨t, ht, hgraph⟩ := stieltjes_completedGraph_intermediate
      traceCyclicAngleLift hab (lt_of_not_ge hleft) (lt_of_not_ge hright)
    refine ⟨t, ⟨ht.1.le, ht.2.le⟩, ?_⟩
    rw [traceBoundaryPath_normals_eq_lift_arc t ⟨ht.1, ht.2.le.trans hb⟩]
    exact ⟨φ, hgraph, rfl⟩
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hgraph : φ ∈ Icc (Function.leftLim traceCyclicAngleLift a)
        (traceCyclicAngleLift b) := by
      simpa only [traceBoundaryIncomingAngle, if_neg ha0] using hφ
    obtain ⟨t, ht, htf⟩ := completedGraph_exists_mem_Icc traceCyclicAngleLift hab hgraph
    refine ⟨t, ht, ?_⟩
    rw [traceBoundaryPath_normals_eq_lift_arc t ⟨ha'.trans_le ht.1, ht.2.trans hb⟩]
    exact ⟨φ, htf, rfl⟩

/-- Every Euclidean unit direction is a genuine supporting normal at
some actual point of the trace unit boundary. -/
theorem traceBoundary_support_exists_of_unit_normal
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1) :
    ∃ t ∈ Icc (0 : ℝ) 4, z ∈ normalsOn traceBasis {traceBoundaryPath t} := by
  obtain ⟨φ, hφeq, hφangle⟩ :=
    exists_circleNormal_eq_and_abs_sub_eq_angle z hz (traceCyclicAngleLift 0)
  have hnear : |φ - traceCyclicAngleLift 0| ≤ Real.pi := by
    rw [hφangle]
    exact InnerProductGeometry.angle_le_pi _ _
  have hnear' := abs_le.mp hnear
  have hperiod := traceCyclicAngleLift_period_increment
  have hincoming := traceBoundaryIncomingAngle_le 0
  by_cases hlow : φ < traceCyclicAngleLift 0
  · have hφ : φ + 2 * Real.pi ∈
        Icc (traceBoundaryIncomingAngle 0) (traceCyclicAngleLift 4) := by
      constructor <;> linarith [hnear'.1, Real.pi_pos]
    obtain ⟨t, ht, hn⟩ := traceBoundary_closedArc_support_exists
      0 4 (φ + 2 * Real.pi) (by norm_num) (by norm_num) (by norm_num) hφ
    exact ⟨t, ht, by simpa only [circleNormal_add_two_pi, ← hφeq] using hn⟩
  · have hφ : φ ∈ Icc (traceBoundaryIncomingAngle 0) (traceCyclicAngleLift 4) := by
      constructor <;> linarith [hnear'.2, Real.pi_pos]
    obtain ⟨t, ht, hn⟩ := traceBoundary_closedArc_support_exists
      0 4 φ (by norm_num) (by norm_num) (by norm_num) hφ
    exact ⟨t, ht, by simpa only [← hφeq] using hn⟩

end Markov
