import Markov.CircularNormalSeparation
import Markov.TraceNormalArcClosure
import Markov.TraceCornerEstimate

/-! Normal separation for ordered actual trace-boundary arcs whose
terminal endpoints are cutoff corners. The two terminal corner jumps
control the forward and wrapped circular gaps. Consequently the paper's
basic parameter assumption makes their closed angular neighborhoods
disjoint, with the full quantitative gap. -/

noncomputable section
open Set

namespace Markov

/-- Distinct ordered trace arcs have normal closures separated by the
actual uniform cutoff-corner turn bound in both circular directions. -/
theorem trace_ordered_cutoff_arcs_normal_closure_separation
    (H a b c d : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d) (hd : d ≤ 4)
    (hbcut : traceBoundaryPath b ∈ realCutoffCorners traceBasis H)
    (hdcut : traceBoundaryPath d ∈ realCutoffCorners traceBasis H)
    (y y' : EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ closure (normalsOn traceBasis (traceBoundaryOpenArc a b)))
    (hy' : y' ∈ closure (normalsOn traceBasis (traceBoundaryOpenArc c d))) :
    traceCornerLowerConstant * Real.exp (-(2 * traceAxisLength * H)) ≤
      InnerProductGeometry.angle y y' := by
  have hb4 : b ≤ 4 := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hbI : b ∈ Ioc (0 : ℝ) 4 := ⟨by linarith, hb4⟩
  have hdI : d ∈ Ioc (0 : ℝ) 4 := ⟨by linarith, hd⟩
  have hjumpb := trace_real_cutoff_corner_atom_lower H (traceBoundaryPath b) hbcut
  have hjumpd := trace_real_cutoff_corner_atom_lower H (traceBoundaryPath d) hdcut
  rw [traceBoundaryTurn_singleton_toReal_eq_jump b hbI] at hjumpb
  rw [traceBoundaryTurn_singleton_toReal_eq_jump d hdI] at hjumpd
  rw [closure_normalsOn_traceBoundaryOpenArc a b ha hab hb4] at hy
  rw [closure_normalsOn_traceBoundaryOpenArc c d hc0 hcd hd] at hy'
  obtain ⟨θ, hθ, rfl⟩ := hy
  obtain ⟨φ, hφ, rfl⟩ := hy'
  have hleftb : Function.leftLim traceCyclicAngleLift b ≤ traceCyclicAngleLift b :=
    traceCyclicAngleLift.mono.leftLim_le le_rfl
  have hleftd : Function.leftLim traceCyclicAngleLift d ≤ traceCyclicAngleLift d :=
    traceCyclicAngleLift.mono.leftLim_le le_rfl
  have hFbc := traceCyclicAngleLift.mono hbc
  have hFd4 := traceCyclicAngleLift.mono hd
  have hF0a := traceCyclicAngleLift.mono ha
  have hperiod := traceCyclicAngleLift_period_increment
  apply angle_circleNormal_ge_of_interval_separation
    (traceCyclicAngleLift a) (Function.leftLim traceCyclicAngleLift b)
    (traceCyclicAngleLift c) (Function.leftLim traceCyclicAngleLift d)
    (traceCornerLowerConstant * Real.exp (-(2 * traceAxisLength * H))) θ φ
    (traceCyclicAngleLift.mono.le_leftLim hab) (hleftb.trans hFbc)
    (traceCyclicAngleLift.mono.le_leftLim hcd) (by linarith)
    (by linarith) (by linarith) hθ hφ

/-- Actual support normals on every trace-boundary open arc are unit
vectors in the original Euclidean covector coordinates. -/
theorem traceBoundaryOpenArc_normals_unit (a b : ℝ)
    (y : EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ normalsOn traceBasis (traceBoundaryOpenArc a b)) : ‖y‖ = 1 := by
  apply norm_eq_one_of_mem_normalsOn traceBasis (traceBoundaryOpenArc a b) _ y hy
  rintro x ⟨t, _, rfl⟩
  exact norm_traceBoundaryPath t

/-- The paper's parameter inequality leaves a gap of at least `ε * η`
between the two actual closed angular neighborhoods. -/
theorem trace_ordered_cutoff_arcs_angular_neighborhood_gap
    (H a b c d ε η : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d) (hd : d ≤ 4)
    (hbcut : traceBoundaryPath b ∈ realCutoffCorners traceBasis H)
    (hdcut : traceBoundaryPath d ∈ realCutoffCorners traceBasis H)
    (hbasic : (2 + ε) * η ≤
      traceCornerLowerConstant * Real.exp (-(2 * traceAxisLength * H)))
    (z z' : EuclideanSpace ℝ (Fin 2))
    (hz : z ∈ closedAngularNeighborhood
      (normalsOn traceBasis (traceBoundaryOpenArc a b)) η)
    (hz' : z' ∈ closedAngularNeighborhood
      (normalsOn traceBasis (traceBoundaryOpenArc c d)) η) :
    ε * η ≤ InnerProductGeometry.angle z z' := by
  have hb4 : b ≤ 4 := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hgap := closedAngularNeighborhood_angle_separation
    (normalsOn traceBasis (traceBoundaryOpenArc a b))
    (normalsOn traceBasis (traceBoundaryOpenArc c d))
    (traceBoundaryOpenArc_normals_isConnected a b ha hab hb4).1
    (traceBoundaryOpenArc_normals_isConnected c d hc0 hcd hd).1
    (traceBoundaryOpenArc_normals_unit a b) (traceBoundaryOpenArc_normals_unit c d)
    (traceCornerLowerConstant * Real.exp (-(2 * traceAxisLength * H))) η
    (fun y hy y' hy' => trace_ordered_cutoff_arcs_normal_closure_separation H a b c d
      ha hab hbc hcd hd hbcut hdcut y y' hy hy') z z' hz hz'
  nlinarith

/-- Positive error and margin parameters in the paper's basic assumption
make the actual closed normal neighborhoods of ordered cutoff arcs disjoint. -/
theorem trace_ordered_cutoff_arcs_angular_neighborhood_disjoint
    (H a b c d ε η : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d) (hd : d ≤ 4)
    (hbcut : traceBoundaryPath b ∈ realCutoffCorners traceBasis H)
    (hdcut : traceBoundaryPath d ∈ realCutoffCorners traceBasis H)
    (hε : 0 < ε) (hη : 0 < η)
    (hbasic : (2 + ε) * η ≤
      traceCornerLowerConstant * Real.exp (-(2 * traceAxisLength * H))) :
    Disjoint
      (closedAngularNeighborhood (normalsOn traceBasis (traceBoundaryOpenArc a b)) η)
      (closedAngularNeighborhood (normalsOn traceBasis (traceBoundaryOpenArc c d)) η) := by
  have hb4 : b ≤ 4 := by linarith
  have hc0 : 0 ≤ c := by linarith
  apply disjoint_closedAngularNeighborhood_of_angle_separation
    (normalsOn traceBasis (traceBoundaryOpenArc a b))
    (normalsOn traceBasis (traceBoundaryOpenArc c d))
    (traceBoundaryOpenArc_normals_isConnected a b ha hab hb4).1
    (traceBoundaryOpenArc_normals_isConnected c d hc0 hcd hd).1
    (traceBoundaryOpenArc_normals_unit a b) (traceBoundaryOpenArc_normals_unit c d)
    (traceCornerLowerConstant * Real.exp (-(2 * traceAxisLength * H))) η
    (fun y hy y' hy' => trace_ordered_cutoff_arcs_normal_closure_separation H a b c d
      ha hab hbc hcd hd hbcut hdcut y y' hy hy')
  nlinarith [mul_pos hε hη]

end Markov
