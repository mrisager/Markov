import Markov.NormalClosureProximity
import Mathlib.Topology.Order.Compact

/-! Closed angular neighborhoods of actual unit-normal sets. The distance
is the infimum over the actual set. Compactness attains that infimum in its
closure, so the exact radius is retained without asserting attainment in
an open normal set. No unresolved-direction predicate is defined here. -/

noncomputable section
open Set

namespace Markov

/-- Angular distance to an actual normal set. Its geometric applications
use a nonempty set of unit normals. -/
def angularDistanceToSet (z : EuclideanSpace ℝ (Fin 2))
    (J : Set (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  sInf ((fun y => InnerProductGeometry.angle y z) '' J)

/-- The closed angular neighborhood, expressed by an infimum over the
actual set, rather than an assumed attained actual-normal witness. -/
def closedAngularNeighborhood (J : Set (EuclideanSpace ℝ (Fin 2))) (η : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | ‖z‖ = 1 ∧ angularDistanceToSet z J ≤ η}

theorem angularDistanceToSet_image_bddBelow (z : EuclideanSpace ℝ (Fin 2))
    (J : Set (EuclideanSpace ℝ (Fin 2))) :
    BddBelow ((fun y => InnerProductGeometry.angle y z) '' J) := by
  refine ⟨0, ?_⟩
  rintro a ⟨y, _, rfl⟩
  exact InnerProductGeometry.angle_nonneg y z

theorem angularDistanceToSet_nonneg (z : EuclideanSpace ℝ (Fin 2))
    (J : Set (EuclideanSpace ℝ (Fin 2))) (hJ : J.Nonempty) :
    0 ≤ angularDistanceToSet z J := by
  apply le_csInf (hJ.image _)
  rintro a ⟨y, _, rfl⟩
  exact InnerProductGeometry.angle_nonneg y z

/-- Closure preserves unit length, ensuring that the angle remains
continuous at every point where the infimum will be attained. -/
theorem norm_eq_one_of_mem_closure_unit_set
    (J : Set (EuclideanSpace ℝ (Fin 2))) (hunit : ∀ y ∈ J, ‖y‖ = 1)
    (y : EuclideanSpace ℝ (Fin 2)) (hy : y ∈ closure J) : ‖y‖ = 1 :=
  closure_minimal hunit (isClosed_eq continuous_norm continuous_const) hy

theorem angle_continuousOn_closure_unit_set
    (J : Set (EuclideanSpace ℝ (Fin 2))) (hunit : ∀ y ∈ J, ‖y‖ = 1)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1) :
    ContinuousOn (fun y => InnerProductGeometry.angle y z) (closure J) := by
  intro y hy
  have hyne : y ≠ 0 := by
    intro hyzero
    have hu := norm_eq_one_of_mem_closure_unit_set J hunit y hy
    simp [hyzero] at hu
  have hzne : z ≠ 0 := by intro hzzero; simp [hzzero] at hz
  exact ((InnerProductGeometry.continuousAt_angle hyne hzne).comp
    (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt

/-- The angular infimum is a lower bound at every closure normal. -/
theorem angularDistanceToSet_le_angle_of_mem_closure
    (J : Set (EuclideanSpace ℝ (Fin 2))) (hunit : ∀ y ∈ J, ‖y‖ = 1)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1)
    (y : EuclideanSpace ℝ (Fin 2)) (hy : y ∈ closure J) :
    angularDistanceToSet z J ≤ InnerProductGeometry.angle y z := by
  apply ContinuousWithinAt.closure_le hy continuousWithinAt_const
    ((angle_continuousOn_closure_unit_set J hunit z hz y hy).mono subset_closure)
  intro w hw
  exact csInf_le (angularDistanceToSet_image_bddBelow z J) ⟨w, hw, rfl⟩

/-- Taking closure does not change the infimal angular distance. -/
theorem angularDistanceToSet_closure_eq
    (J : Set (EuclideanSpace ℝ (Fin 2))) (hJ : J.Nonempty)
    (hunit : ∀ y ∈ J, ‖y‖ = 1) (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1) :
    angularDistanceToSet z (closure J) = angularDistanceToSet z J := by
  apply le_antisymm
  · apply le_csInf (hJ.image _)
    rintro a ⟨y, hy, rfl⟩
    exact csInf_le (angularDistanceToSet_image_bddBelow z (closure J))
      ⟨y, subset_closure hy, rfl⟩
  · apply le_csInf (hJ.closure.image _)
    rintro a ⟨y, hy, rfl⟩
    exact angularDistanceToSet_le_angle_of_mem_closure J hunit z hz y hy

/-- The angular distance to a nonempty unit-normal set is attained in
its compact closure, at exactly the infimal radius. -/
theorem exists_mem_closure_angle_eq_angularDistanceToSet
    (J : Set (EuclideanSpace ℝ (Fin 2))) (hJ : J.Nonempty)
    (hunit : ∀ y ∈ J, ‖y‖ = 1) (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1) :
    ∃ y ∈ closure J, InnerProductGeometry.angle y z = angularDistanceToSet z J := by
  have hcompact : IsCompact (closure J) :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).of_isClosed_subset
      isClosed_closure (by
        intro y hy
        rw [Metric.mem_closedBall, dist_zero_right,
          norm_eq_one_of_mem_closure_unit_set J hunit y hy])
  obtain ⟨y, hy, hmin⟩ := hcompact.exists_isMinOn hJ.closure
    (angle_continuousOn_closure_unit_set J hunit z hz)
  refine ⟨y, hy, le_antisymm ?_ (angularDistanceToSet_le_angle_of_mem_closure
    J hunit z hz y hy)⟩
  apply le_csInf (hJ.image _)
  rintro a ⟨w, hw, rfl⟩
  exact hmin (subset_closure hw)

/-- Exact closed-neighborhood membership is equivalent to a witness in
the closure. No witness in the actual set is asserted. -/
theorem mem_closedAngularNeighborhood_iff_exists_mem_closure
    (J : Set (EuclideanSpace ℝ (Fin 2))) (hJ : J.Nonempty)
    (hunit : ∀ y ∈ J, ‖y‖ = 1) (z : EuclideanSpace ℝ (Fin 2)) (η : ℝ) :
    z ∈ closedAngularNeighborhood J η ↔
      ‖z‖ = 1 ∧ ∃ y ∈ closure J, InnerProductGeometry.angle y z ≤ η := by
  constructor
  · rintro ⟨hz, hd⟩
    obtain ⟨y, hy, he⟩ := exists_mem_closure_angle_eq_angularDistanceToSet J hJ hunit z hz
    exact ⟨hz, y, hy, he.trans_le hd⟩
  · rintro ⟨hz, y, hy, hangle⟩
    exact ⟨hz, (angularDistanceToSet_le_angle_of_mem_closure J hunit z hz y hy).trans hangle⟩

end Markov
