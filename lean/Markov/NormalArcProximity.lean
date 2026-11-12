import Markov.BoundaryNormals
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Metric proximity to selected endpoint normals of actual boundary arcs.
Endpoint membership in the closure is supplied by `BoundaryNormals`. The
remaining inputs are an explicit nearby actual normal and an upper bound
for the diameter of the actual normal set. -/

noncomputable section
open Set

namespace Markov

/-- A point of the closure is no farther from any point of a bounded set
than the diameter of that set. -/
theorem dist_le_diam_of_mem_closure {X : Type*} [PseudoMetricSpace X]
    {S : Set X} (hS : Bornology.IsBounded S) {x y : X}
    (hx : x ∈ closure S) (hy : y ∈ S) : dist x y ≤ Metric.diam S := by
  calc
    dist x y ≤ Metric.diam (closure S) :=
      Metric.dist_le_diam_of_mem hS.closure hx (subset_closure hy)
    _ = Metric.diam S := Metric.diam_closure S

/-- A diameter estimate transfers proximity of one actual point to every
point of the closure. The witness also makes any sign constraints on the
proximity radius explicit consequences rather than extra assumptions. -/
theorem dist_le_add_of_mem_closure_of_exists_near {X : Type*} [PseudoMetricSpace X]
    {S : Set X} (hS : Bornology.IsBounded S) {x z : X} (hx : x ∈ closure S)
    (T η : ℝ) (hdiam : Metric.diam S ≤ T)
    (hnear : ∃ y ∈ S, dist y z ≤ η) : dist x z ≤ T + η := by
  obtain ⟨y, hy, hyz⟩ := hnear
  calc
    dist x z ≤ dist x y + dist y z := dist_triangle x y z
    _ ≤ T + η := add_le_add ((dist_le_diam_of_mem_closure hS hx hy).trans hdiam) hyz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalization has norm at most one, also for a zero functional. -/
theorem norm_normalizedEuclideanCovector_le_one (C : Module.Basis (Fin 2) ℝ E)
    (f : StrongDual ℝ E) : ‖normalizedEuclideanCovector C f‖ ≤ 1 := by
  by_cases hzero : euclideanDualCoordinates C f = 0
  · simp [normalizedEuclideanCovector, hzero]
  · exact (NormedSpace.norm_normalize hzero).le

theorem normalsOn_subset_closedBall (C : Module.Basis (Fin 2) ℝ E) (S : Set E) :
    normalsOn C S ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  rintro n ⟨_, _, f, _, rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    norm_normalizedEuclideanCovector_le_one C f

/-- All actual normal sets are bounded, without restrictions on their
underlying point set. -/
theorem normalsOn_isBounded (C : Module.Basis (Fin 2) ℝ E) (S : Set E) :
    Bornology.IsBounded (normalsOn C S) :=
  Metric.isBounded_closedBall.subset (normalsOn_subset_closedBall C S)

/-- Proximity to an actual normal of the local boundary arc transfers to
its selected endpoint normal. The endpoint closure is a proved conclusion
of the norming-support limit theorem. -/
theorem selectedSupport_normal_dist_le_add
    (B C : Module.Basis (Fin 2) ℝ E) (ε : ℝ) (hε : 0 < ε)
    (z : EuclideanSpace ℝ (Fin 2)) (T η : ℝ)
    (hdiam : Metric.diam (normalsOn C (slopeBoundaryArc B 0 ε)) ≤ T)
    (hnear : ∃ y ∈ normalsOn C (slopeBoundaryArc B 0 ε), dist y z ≤ η) :
    dist (normalizedEuclideanCovector C (selectedSupport B)) z ≤ T + η := by
  exact dist_le_add_of_mem_closure_of_exists_near
    (normalsOn_isBounded C (slopeBoundaryArc B 0 ε))
    (selectedSupport_normal_mem_closure_normalsOn_slopeBoundaryArc B C ε hε)
    T η hdiam hnear

/-- Direct frontier-wedge formulation of the same metric transfer. -/
theorem selectedSupport_normal_dist_le_add_frontier_wedge
    (B C : Module.Basis (Fin 2) ℝ E) (ε : ℝ) (hε : 0 < ε)
    (z : EuclideanSpace ℝ (Fin 2)) (T η : ℝ)
    (hdiam : Metric.diam (normalsOn C (frontier (Metric.closedBall (0 : E) 1) ∩
      {x | 0 < B.coord 0 x ∧ 0 < basisSlope B x ∧ basisSlope B x < ε})) ≤ T)
    (hnear : ∃ y ∈ normalsOn C (frontier (Metric.closedBall (0 : E) 1) ∩
      {x | 0 < B.coord 0 x ∧ 0 < basisSlope B x ∧ basisSlope B x < ε}), dist y z ≤ η) :
    dist (normalizedEuclideanCovector C (selectedSupport B)) z ≤ T + η := by
  rw [← slopeBoundaryArc_eq_frontier_wedge] at hdiam hnear
  exact selectedSupport_normal_dist_le_add B C ε hε z T η hdiam hnear

/-- Independent integral rays have the same proximity estimate on their
actual local boundary arc. -/
theorem selectedSupportAt_normal_dist_le_add
    (B C : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ) (hdet : intDet u v ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (z : EuclideanSpace ℝ (Fin 2)) (T η : ℝ)
    (hdiam : Metric.diam
      (normalsOn C (slopeBoundaryArc (intPairBasis B u v hdet) 0 ε)) ≤ T)
    (hnear : ∃ y ∈ normalsOn C (slopeBoundaryArc (intPairBasis B u v hdet) 0 ε),
      dist y z ≤ η) :
    dist (normalizedEuclideanCovector C (selectedSupportAt B u v)) z ≤ T + η := by
  rw [selectedSupportAt, dif_pos hdet]
  exact selectedSupport_normal_dist_le_add (intPairBasis B u v hdet) C ε hε z T η hdiam hnear

end Markov
