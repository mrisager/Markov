import Markov.NormingCovectorRadius
import Markov.BoundaryNormals

/-! The actual trace unit ball in the fixed Euclidean coordinates and
the supporting-line inequalities supplied by its genuine norming normals. -/

noncomputable section
open Set
namespace Markov

/-- The constructed trace unit ball expressed in the fixed Euclidean
coordinates, with its original norm unchanged. -/
def traceEuclideanBall : Set (EuclideanSpace ℝ (Fin 2)) :=
  traceEuclideanCoordinates '' Metric.closedBall (0 : TracePlane) 1

theorem traceEuclideanCoordinates_mem_ball (x : TracePlane) (hx : ‖x‖ ≤ 1) :
    traceEuclideanCoordinates x ∈ traceEuclideanBall :=
  ⟨x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx, rfl⟩

theorem zero_mem_traceEuclideanBall : (0 : EuclideanSpace ℝ (Fin 2)) ∈ traceEuclideanBall := by
  simpa only [map_zero] using traceEuclideanCoordinates_mem_ball 0 (by simp)

theorem traceEuclideanBall_nonempty : traceEuclideanBall.Nonempty :=
  ⟨0, zero_mem_traceEuclideanBall⟩

theorem isCompact_traceEuclideanBall : IsCompact traceEuclideanBall := by
  letI : FiniteDimensional ℝ TracePlane := traceBasis.finiteDimensional_of_finite
  exact (isCompact_closedBall (0 : TracePlane) 1).image traceEuclideanCoordinates.continuous

/-- Evaluation against a normalized actual covector in Euclidean
coordinates is its original functional evaluation times a nonnegative factor. -/
theorem traceSupport_normalized_inner_coordinates
    (f : StrongDual ℝ TracePlane) (x : TracePlane) :
    inner ℝ (traceEuclideanCoordinates x) (normalizedEuclideanCovector traceBasis f) =
      ‖euclideanDualCoordinates traceBasis f‖⁻¹ * f x := by
  rw [normalizedEuclideanCovector, NormedSpace.normalize, inner_smul_right,
    real_inner_comm, ← traceSupport_eval_eq_inner_coordinates]

/-- A genuine norming functional at an actual unit point supplies a
supporting line for every point of the actual Euclidean trace ball. -/
theorem traceEuclideanBall_support_of_normingFunctional
    (x : TracePlane) (hx : ‖x‖ = 1)
    (f : StrongDual ℝ TracePlane) (hf : f ∈ normingFunctionals x)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ traceEuclideanBall) :
    inner ℝ (z - traceEuclideanCoordinates x) (normalizedEuclideanCovector traceBasis f) ≤ 0 := by
  rcases hz with ⟨y, hy, rfl⟩
  have hy' : ‖y‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have hfy := normingFunctional_on_unitBall x f hf y hy'
  rw [← map_sub, traceSupport_normalized_inner_coordinates, map_sub, hf.2, hx]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) (by linarith)

/-- Every actual normal over a singleton point yields its associated
Euclidean unit support point and the supporting inequality on the whole ball. -/
theorem traceEuclideanBall_support_of_mem_normalsOn_singleton
    (x : TracePlane) (hx : ‖x‖ = 1) (n : EuclideanSpace ℝ (Fin 2))
    (hn : n ∈ normalsOn traceBasis {x}) :
    traceEuclideanCoordinates x ∈ traceEuclideanBall ∧ ‖n‖ = 1 ∧
      ∀ z ∈ traceEuclideanBall, inner ℝ (z - traceEuclideanCoordinates x) n ≤ 0 := by
  rcases hn with ⟨y, hy, f, hf, rfl⟩
  have hyx : y = x := hy
  subst y
  refine ⟨traceEuclideanCoordinates_mem_ball x hx.le, ?_, ?_⟩
  · exact norm_normalizedEuclideanCovector_of_norming traceBasis x
      (by intro he; simp [he] at hx) f hf
  · exact traceEuclideanBall_support_of_normingFunctional x hx f hf

/-- The maximum Euclidean support height of the actual trace ball. -/
def traceEuclideanSupportHeight (n : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  sSup ((fun z => inner ℝ z n) '' traceEuclideanBall)

theorem inner_le_traceEuclideanSupportHeight
    (n z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ traceEuclideanBall) :
    inner ℝ z n ≤ traceEuclideanSupportHeight n := by
  apply le_csSup
  · exact (isCompact_traceEuclideanBall.image
      (continuous_id.inner continuous_const)).bddAbove
  · exact ⟨z, hz, rfl⟩

/-- The support height is attained on the actual compact image ball. -/
theorem traceEuclideanSupportHeight_exists_mem
    (n : EuclideanSpace ℝ (Fin 2)) :
    ∃ p ∈ traceEuclideanBall, inner ℝ p n = traceEuclideanSupportHeight n := by
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin 2) => inner ℝ z n) :=
    continuous_id.inner continuous_const
  obtain ⟨p, hp, hmax⟩ := isCompact_traceEuclideanBall.exists_isMaxOn
    traceEuclideanBall_nonempty hc.continuousOn
  refine ⟨p, hp, le_antisymm (inner_le_traceEuclideanSupportHeight n p hp) ?_⟩
  apply csSup_le (traceEuclideanBall_nonempty.image _)
  rintro _ ⟨z, hz, rfl⟩
  exact hmax hz

/-- A given actual singleton normal identifies the support height with
the height of that same associated boundary point. -/
theorem traceEuclideanSupportHeight_eq_of_mem_normalsOn_singleton
    (x : TracePlane) (hx : ‖x‖ = 1) (n : EuclideanSpace ℝ (Fin 2))
    (hn : n ∈ normalsOn traceBasis {x}) :
    traceEuclideanSupportHeight n = inner ℝ (traceEuclideanCoordinates x) n := by
  obtain ⟨hp, _, hs⟩ := traceEuclideanBall_support_of_mem_normalsOn_singleton x hx n hn
  apply le_antisymm
  · apply csSup_le (traceEuclideanBall_nonempty.image _)
    rintro _ ⟨z, hz, rfl⟩
    have h := hs z hz
    rw [inner_sub_left] at h
    linarith
  · exact inner_le_traceEuclideanSupportHeight n _ hp

end Markov
