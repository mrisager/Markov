import Markov.ClosedAngularNeighborhood
import Markov.TraceCutoffClosureHeight

/-! The canonical-sector endpoint-height estimate for a point in the
closed angular neighborhood of the cutoff normal set. Compactness gives
the neighborhood witness in the closure of the set. -/

noncomputable section
open Set
namespace Markov

theorem traceCutoffArc_normals_nonempty (n : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes n u v) :
    (normalsOn traceBasis (traceCutoffArc u v)).Nonempty := by
  obtain ⟨x, hx⟩ := traceCutoffArc_nonempty n u v h
  obtain ⟨f, hf⟩ := normingFunctionals_nonempty x
  exact ⟨normalizedEuclideanCovector traceBasis f, x, hx, f, hf, rfl⟩

/-- Canonical cutoff angular-neighborhood membership gives the exact
closure-angle witness, even if its infimum is not attained on the open arc. -/
theorem trace_cutoff_angular_neighborhood_witness
    (n : ℕ) (u v d : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v) (η : ℝ)
    (hmem : NormedSpace.normalize (euclideanIntDirection d) ∈
      closedAngularNeighborhood (normalsOn traceBasis (traceCutoffArc u v)) η) :
    ∃ y ∈ closure (normalsOn traceBasis (traceCutoffArc u v)),
      InnerProductGeometry.angle y (NormedSpace.normalize (euclideanIntDirection d)) ≤ η := by
  exact ((mem_closedAngularNeighborhood_iff_exists_mem_closure _
    (traceCutoffArc_normals_nonempty n u v h)
    (norm_eq_one_of_mem_trace_cutoff_normals u v) _ η).mp hmem).2

/-- The local canonical-sector height estimate now takes actual angular
neighborhood membership instead of an assumed nearby-normal witness.
Only the explicit exponential error bound remains an analytic parameter input. -/
theorem trace_canonical_angular_neighborhood_height_bound :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (u v d : ℤ × ℤ), ConsecutiveCutoffSlopes n u v → d ≠ (0, 0) →
      ∀ (A N η : ℝ), 1 ≤ A → intHeight u ≤ A →
      NormedSpace.normalize (euclideanIntDirection d) ∈
        closedAngularNeighborhood (normalsOn traceBasis (traceCutoffArc u v)) η →
      η ≤ N * Real.exp (-c * (n : ℝ)) →
      0 < (traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c ∧
        (n : ℝ) ≤
          ((traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c) *
            intEuclidean d * A ^ 2 := by
  obtain ⟨M, c, hM, hc, hheight⟩ := trace_cutoff_angle_near_closure_height_bound
  refine ⟨M, c, hM, hc, ?_⟩
  intro n hn u v d h hd A N η hA hu hmem hη
  exact hheight n hn u v d h hd A N η hA hu
    (trace_cutoff_angular_neighborhood_witness n u v d h η hmem) hη

end Markov
