import Markov.AngularNormals

/-! Exact proximity estimates with witnesses in the closure of an actual
normal set. A closed angular neighborhood of normals along an open arc can
contain a direction whose closest normal occurs only as an endpoint limit.
The closure witness below retains the given radius without asserting an
attained witness among the actual interior normals. -/

noncomputable section
open Set

namespace Markov

/-- Two points of the closure of a bounded set are separated by at most
the diameter of the original set. -/
theorem dist_le_diam_of_mem_closure_pair {X : Type*} [PseudoMetricSpace X]
    {S : Set X} (hS : Bornology.IsBounded S) {x y : X}
    (hx : x ∈ closure S) (hy : y ∈ closure S) : dist x y ≤ Metric.diam S := by
  calc
    dist x y ≤ Metric.diam (closure S) := Metric.dist_le_diam_of_mem hS.closure hx hy
    _ = Metric.diam S := Metric.diam_closure S

/-- A nearby closure point and a diameter estimate control every point
of the closure, at the original proximity radius. -/
theorem dist_le_add_of_mem_closure_of_exists_near_closure
    {X : Type*} [PseudoMetricSpace X] {S : Set X}
    (hS : Bornology.IsBounded S) {x z : X} (hx : x ∈ closure S)
    (T η : ℝ) (hdiam : Metric.diam S ≤ T)
    (hnear : ∃ y ∈ closure S, dist y z ≤ η) : dist x z ≤ T + η := by
  obtain ⟨y, hy, hyz⟩ := hnear
  exact (dist_triangle x y z).trans
    (add_le_add ((dist_le_diam_of_mem_closure_pair hS hx hy).trans hdiam) hyz)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Unit length persists under closure for normals over unit-boundary
points. This is independent of the norm used on the source plane. -/
theorem norm_eq_one_of_mem_closure_normalsOn
    (C : Module.Basis (Fin 2) ℝ E) (S : Set E)
    (hS : ∀ x ∈ S, ‖x‖ = 1) (n : EuclideanSpace ℝ (Fin 2))
    (hn : n ∈ closure (normalsOn C S)) : ‖n‖ = 1 := by
  have hsub : normalsOn C S ⊆ {y : EuclideanSpace ℝ (Fin 2) | ‖y‖ = 1} := by
    intro y hy
    exact norm_eq_one_of_mem_normalsOn C S hS y hy
  exact closure_minimal hsub (isClosed_eq continuous_norm continuous_const) hn

/-- A nearby point in the closed actual normal set controls any endpoint
normal already known to belong to that same closure. -/
theorem normal_dist_le_add_of_mem_closure_of_exists_near_closure
    (C : Module.Basis (Fin 2) ℝ E) (S : Set E)
    (x z : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ closure (normalsOn C S))
    (T η : ℝ) (hdiam : Metric.diam (normalsOn C S) ≤ T)
    (hnear : ∃ y ∈ closure (normalsOn C S), dist y z ≤ η) :
    dist x z ≤ T + η :=
  dist_le_add_of_mem_closure_of_exists_near_closure (normalsOn_isBounded C S)
    hx T η hdiam hnear

/-- An angular witness in the closure of the normal set gives
the stated Euclidean proximity bound. -/
theorem normal_dist_le_add_of_mem_closure_of_exists_angle_near_closure
    (C : Module.Basis (Fin 2) ℝ E) (S : Set E)
    (hS : ∀ w ∈ S, ‖w‖ = 1) (x z : EuclideanSpace ℝ (Fin 2))
    (hx : x ∈ closure (normalsOn C S)) (hz : ‖z‖ = 1)
    (T η : ℝ) (hdiam : Metric.diam (normalsOn C S) ≤ T)
    (hnear : ∃ y ∈ closure (normalsOn C S), InnerProductGeometry.angle y z ≤ η) :
    dist x z ≤ T + η := by
  apply normal_dist_le_add_of_mem_closure_of_exists_near_closure C S x z hx T η hdiam
  obtain ⟨y, hy, hyz⟩ := hnear
  exact ⟨y, hy, (dist_le_angle_of_norm_eq_one y z
    (norm_eq_one_of_mem_closure_normalsOn C S hS y hy) hz).trans hyz⟩

/-- The selected endpoint normal has the exact closure-witness estimate
on every actual local slope arc. -/
theorem selectedSupport_normal_dist_le_add_of_near_closure
    (B C : Module.Basis (Fin 2) ℝ E) (ε : ℝ) (hε : 0 < ε)
    (z : EuclideanSpace ℝ (Fin 2)) (T η : ℝ)
    (hdiam : Metric.diam (normalsOn C (slopeBoundaryArc B 0 ε)) ≤ T)
    (hnear : ∃ y ∈ closure (normalsOn C (slopeBoundaryArc B 0 ε)), dist y z ≤ η) :
    dist (normalizedEuclideanCovector C (selectedSupport B)) z ≤ T + η :=
  normal_dist_le_add_of_mem_closure_of_exists_near_closure C _ _ z
    (selectedSupport_normal_mem_closure_normalsOn_slopeBoundaryArc B C ε hε)
    T η hdiam hnear

/-- The same exact estimate for an actual integral selected support,
with the original source norm and arbitrary Euclidean coordinate basis. -/
theorem selectedSupportAt_normal_dist_le_add_of_near_closure
    (B C : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ) (hdet : intDet u v ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (z : EuclideanSpace ℝ (Fin 2)) (T η : ℝ)
    (hdiam : Metric.diam
      (normalsOn C (slopeBoundaryArc (intPairBasis B u v hdet) 0 ε)) ≤ T)
    (hnear : ∃ y ∈ closure
      (normalsOn C (slopeBoundaryArc (intPairBasis B u v hdet) 0 ε)), dist y z ≤ η) :
    dist (normalizedEuclideanCovector C (selectedSupportAt B u v)) z ≤ T + η := by
  rw [selectedSupportAt, dif_pos hdet]
  exact selectedSupport_normal_dist_le_add_of_near_closure
    (intPairBasis B u v hdet) C ε hε z T η hdiam hnear

end Markov
