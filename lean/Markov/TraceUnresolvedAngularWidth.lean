import Markov.TraceCutoffNormalSeparation
import Markov.TraceCutoffPathComponents
import Markov.TraceTurnTail

/-! Upper angular widths of actual uncut-component normal neighborhoods.
The exact normal closure interval bounds angles by actual open-arc turn;
compact closure witnesses add at most twice the neighborhood radius.
The actual complementary-turn tail supplies a uniform exponential bound. -/

noncomputable section
open Set MeasureTheory

namespace Markov

/-- The ordinary angle between circle normals is no larger than the
absolute difference of any chosen real angle parameters. -/
theorem angle_circleNormal_le_abs_sub (θ φ : ℝ) :
    InnerProductGeometry.angle (circleNormal θ) (circleNormal φ) ≤ |θ - φ| := by
  by_cases hshort : |φ - θ| ≤ Real.pi
  · rw [angle_circleNormal_eq_arccos_cos_sub, ← Real.cos_abs (φ - θ),
      Real.arccos_cos (abs_nonneg _) hshort, abs_sub_comm]
  · exact (InnerProductGeometry.angle_le_pi _ _).trans (by
      rw [abs_sub_comm]
      exact (lt_of_not_ge hshort).le)

/-- An upper bound for all angles in the normal closure enlarges by at
most twice the radius on its actual closed angular neighborhood. -/
theorem closedAngularNeighborhood_angle_le_of_closure_bound
    (J : Set (EuclideanSpace ℝ (Fin 2))) (hJ : J.Nonempty)
    (hunit : ∀ y ∈ J, ‖y‖ = 1) (L η : ℝ)
    (hwidth : ∀ y ∈ closure J, ∀ y' ∈ closure J,
      InnerProductGeometry.angle y y' ≤ L)
    (z z' : EuclideanSpace ℝ (Fin 2))
    (hz : z ∈ closedAngularNeighborhood J η)
    (hz' : z' ∈ closedAngularNeighborhood J η) :
    InnerProductGeometry.angle z z' ≤ L + 2 * η := by
  obtain ⟨_, y, hy, hyz⟩ :=
    (mem_closedAngularNeighborhood_iff_exists_mem_closure J hJ hunit z η).mp hz
  obtain ⟨_, y', hy', hyz'⟩ :=
    (mem_closedAngularNeighborhood_iff_exists_mem_closure J hJ hunit z' η).mp hz'
  have hfirst := InnerProductGeometry.angle_le_angle_add_angle z y z'
  have hsecond := InnerProductGeometry.angle_le_angle_add_angle y y' z'
  rw [InnerProductGeometry.angle_comm z y] at hfirst
  linarith [hwidth y hy y' hy']

/-- The closure of all actual support normals along an open boundary arc
has angular diameter no larger than that arc's actual boundary turn. -/
theorem traceBoundaryOpenArc_normal_closure_angle_le_turn
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 4)
    (y y' : EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ closure (normalsOn traceBasis (traceBoundaryOpenArc a b)))
    (hy' : y' ∈ closure (normalsOn traceBasis (traceBoundaryOpenArc a b))) :
    InnerProductGeometry.angle y y' ≤
      (traceBoundaryTurn (traceBoundaryOpenArc a b)).toReal := by
  rw [closure_normalsOn_traceBoundaryOpenArc a b ha hab hb] at hy hy'
  obtain ⟨θ, hθ, rfl⟩ := hy
  obtain ⟨φ, hφ, rfl⟩ := hy'
  rw [traceBoundaryTurn_openArc_toReal a b ha hab hb]
  apply (angle_circleNormal_le_abs_sub θ φ).trans
  apply abs_le.mpr
  constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2]

/-- The actual closed normal neighborhood of an open arc has angular
diameter bounded by its actual turn plus twice its stated radius. -/
theorem traceBoundaryOpenArc_angular_neighborhood_angle_le_turn
    (a b η : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 4)
    (z z' : EuclideanSpace ℝ (Fin 2))
    (hz : z ∈ closedAngularNeighborhood
      (normalsOn traceBasis (traceBoundaryOpenArc a b)) η)
    (hz' : z' ∈ closedAngularNeighborhood
      (normalsOn traceBasis (traceBoundaryOpenArc a b)) η) :
    InnerProductGeometry.angle z z' ≤
      (traceBoundaryTurn (traceBoundaryOpenArc a b)).toReal + 2 * η := by
  apply closedAngularNeighborhood_angle_le_of_closure_bound
    (normalsOn traceBasis (traceBoundaryOpenArc a b))
    (traceBoundaryOpenArc_normals_isConnected a b ha hab hb).1
    (traceBoundaryOpenArc_normals_unit a b)
    ((traceBoundaryTurn (traceBoundaryOpenArc a b)).toReal) η
    (fun y hy y' hy' => traceBoundaryOpenArc_normal_closure_angle_le_turn
      a b ha hab hb y y' hy hy') z z' hz hz'

/-- Every actual component's closed normal neighborhood has angular
diameter bounded by the entire actual uncut-boundary turn plus twice
the neighborhood radius. No unresolved association uniqueness is used. -/
theorem traceUncutBoundary_component_angular_neighborhood_angle_le_turn
    (H : ℝ) (hH : 1 ≤ H) (x : TracePlane) (hx : x ∈ traceUncutBoundary H)
    (η : ℝ) (z z' : EuclideanSpace ℝ (Fin 2))
    (hz : z ∈ closedAngularNeighborhood
      (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η)
    (hz' : z' ∈ closedAngularNeighborhood
      (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η) :
    InnerProductGeometry.angle z z' ≤
      (traceBoundaryTurn (traceUncutBoundary H)).toReal + 2 * η := by
  obtain ⟨a, b, ha, hab, hb, _, _, hcomp⟩ :=
    traceUncutBoundary_exists_path_component H hH x hx
  rw [hcomp] at hz hz'
  have hwidth := traceBoundaryOpenArc_angular_neighborhood_angle_le_turn
    a b η ha hab hb z z' hz hz'
  have hturn : (traceBoundaryTurn (traceBoundaryOpenArc a b)).toReal ≤
      (traceBoundaryTurn (traceUncutBoundary H)).toReal := by
    rw [← hcomp]
    exact ENNReal.toReal_mono (measure_ne_top traceBoundaryTurn _)
      (measure_mono (connectedComponentIn_subset (traceUncutBoundary H) x))
  linarith

/-- Uniform exponential width for the actual closed angular neighborhood
of every real-cutoff component. All turn and interval estimates are proved;
only the displayed actual neighborhood memberships are hypotheses. -/
theorem traceUncutBoundary_component_angular_neighborhood_exp_width :
    ∃ M κ : ℝ, 0 < M ∧ 0 < κ ∧ ∀ H : ℝ, 1 ≤ H →
      ∀ x : TracePlane, x ∈ traceUncutBoundary H →
      ∀ (η : ℝ) (z z' : EuclideanSpace ℝ (Fin 2)),
      z ∈ closedAngularNeighborhood
        (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η →
      z' ∈ closedAngularNeighborhood
        (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η →
      InnerProductGeometry.angle z z' ≤ M * Real.exp (-(κ * H)) + 2 * η := by
  obtain ⟨M, κ, hM, hκ, htail⟩ := traceBoundary_turn_tail_real
  refine ⟨M, κ, hM, hκ, ?_⟩
  intro H hH x hx η z z' hz hz'
  have hturn : (traceBoundaryTurn (traceUncutBoundary H)).toReal ≤
      M * Real.exp (-(κ * H)) := htail H hH
  exact (traceUncutBoundary_component_angular_neighborhood_angle_le_turn
    H hH x hx η z z' hz hz').trans (add_le_add hturn le_rfl)

end Markov
