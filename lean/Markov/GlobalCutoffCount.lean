import Markov.GlobalCutoffCoverage
import Markov.CutoffGapCount
import Mathlib.Topology.Connected.Clopen
import Mathlib.SetTheory.Cardinal.Finite

/-! The signed cutoff-gap indices bound the number of components
of the complement of the cutoff set in the unit boundary. -/

noncomputable section
namespace Markov

/-- If every actual component belongs to a finite family, inject the
connected-component quotient into that family. -/
theorem connectedComponents_card_le_of_componentIn_mem
    {X : Type*} [TopologicalSpace X] (M : Set X) (S : Finset (Set X))
    (hcover : ∀ x ∈ M, connectedComponentIn M x ∈ S) :
    Finite (ConnectedComponents M) ∧ Nat.card (ConnectedComponents M) ≤ S.card := by
  classical
  let rep : ConnectedComponents M → M :=
    fun c => Classical.choose (ConnectedComponents.surjective_coe c)
  have hrep (c : ConnectedComponents M) : ConnectedComponents.mk (rep c) = c :=
    Classical.choose_spec (ConnectedComponents.surjective_coe c)
  let f : ConnectedComponents M → S :=
    fun c => ⟨connectedComponentIn M (rep c).val, hcover _ (rep c).property⟩
  have hinj : Function.Injective f := by
    intro c d hcd
    have heq : connectedComponentIn M (rep c).val = connectedComponentIn M (rep d).val :=
      congrArg Subtype.val hcd
    rw [connectedComponentIn_eq_image (rep c).property,
      connectedComponentIn_eq_image (rep d).property] at heq
    have himg : Function.Injective (Set.image (Subtype.val : M → X)) :=
      Set.image_injective.mpr Subtype.val_injective
    have hcomp : connectedComponent (rep c) = connectedComponent (rep d) := himg heq
    have hmk := ConnectedComponents.coe_eq_coe.mpr hcomp
    exact (hrep c).symm.trans (hmk.trans (hrep d))
  refine ⟨Finite.of_injective f hinj, ?_⟩
  simpa using Nat.card_le_card_of_injective f hinj

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The finite family of signed arcs indexed by actual consecutive cutoff pairs. -/
def cutoffComponentFamily (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) : Finset (Set E) := by
  classical
  exact (signedGapIndices H).image (fun i =>
    slopeBoundaryArc (signedSectorBasis B i.1) (cutoffSlope i.2.1) (cutoffSlope i.2.2))

/-- Every connected component of the actual boundary complement occurs
in the finite family of signed cutoff arcs. -/
theorem connectedComponentIn_mem_cutoffComponentFamily
    (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) (hH : 1 ≤ H) (x : E)
    (hx : x ∈ frontier (Metric.closedBall (0 : E) 1) \ (↑(cutoffCorners B H) : Set E)) :
    connectedComponentIn
      (frontier (Metric.closedBall (0 : E) 1) \ (↑(cutoffCorners B H) : Set E)) x ∈
        cutoffComponentFamily B H := by
  classical
  obtain ⟨k, u, v, huv, _, hcomp⟩ :=
    uncut_boundary_exists_signed_cutoff_component B H hH x hx
  rw [hcomp]
  exact Finset.mem_image.mpr
    ⟨(k, (u, v)), (mem_signedGapIndices H k u v).mpr huv, rfl⟩

/-- Distinct signed arcs are no more numerous than the arithmetic indices. -/
theorem cutoffComponentFamily_card_le_cutoffSlopes
    (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) :
    (cutoffComponentFamily B H).card ≤ 8 * (cutoffSlopesUpTo H).card := by
  classical
  exact (Finset.card_image_le).trans (signedGapIndices_card_le_cutoffSlopes H)

/-- A quadratic bound for the finite signed arc family. -/
theorem cutoffComponentFamily_card_le
    (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) :
    (cutoffComponentFamily B H).card ≤ 8 * (2 * H + 1) ^ 2 := by
  classical
  exact (Finset.card_image_le).trans (signedGapIndices_card_le H)

/-- Finiteness and the arithmetic-index bound for the actual connected
components of the unit boundary after removing the primitive cutoff. -/
theorem cutoffBoundaryComponents_finite_and_card_le_cutoffSlopes
    (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) (hH : 1 ≤ H) :
    Finite (ConnectedComponents
      (↥(frontier (Metric.closedBall (0 : E) 1) \ (↑(cutoffCorners B H) : Set E)))) ∧
      Nat.card (ConnectedComponents
        (↥(frontier (Metric.closedBall (0 : E) 1) \ (↑(cutoffCorners B H) : Set E)))) ≤
        8 * (cutoffSlopesUpTo H).card := by
  obtain ⟨hfinite, hcard⟩ := connectedComponents_card_le_of_componentIn_mem
    (frontier (Metric.closedBall (0 : E) 1) \ (↑(cutoffCorners B H) : Set E))
    (cutoffComponentFamily B H)
    (connectedComponentIn_mem_cutoffComponentFamily B H hH)
  exact ⟨hfinite, hcard.trans (cutoffComponentFamily_card_le_cutoffSlopes B H)⟩

/-- The actual boundary complement has finitely many connected components. -/
theorem cutoffBoundaryComponents_finite
    (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) (hH : 1 ≤ H) :
    Finite (ConnectedComponents
      (↥(frontier (Metric.closedBall (0 : E) 1) \ (↑(cutoffCorners B H) : Set E)))) :=
  (cutoffBoundaryComponents_finite_and_card_le_cutoffSlopes B H hH).1

/-- A quadratic upper bound for the number of actual connected components. -/
theorem cutoffBoundaryComponents_card_le
    (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) (hH : 1 ≤ H) :
    Nat.card (ConnectedComponents
      (↥(frontier (Metric.closedBall (0 : E) 1) \ (↑(cutoffCorners B H) : Set E)))) ≤
      8 * (2 * H + 1) ^ 2 := by
  exact (cutoffBoundaryComponents_finite_and_card_le_cutoffSlopes B H hH).2.trans
    (Nat.mul_le_mul_left 8 (cutoffSlopesUpTo_card_le H))

/-- For positive cutoffs the component count is at most `72 * H²`. -/
theorem cutoffBoundaryComponents_card_le_mul_sq
    (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) (hH : 1 ≤ H) :
    Nat.card (ConnectedComponents
      (↥(frontier (Metric.closedBall (0 : E) 1) \ (↑(cutoffCorners B H) : Set E)))) ≤
      72 * H ^ 2 := by
  calc
    _ ≤ 8 * (2 * H + 1) ^ 2 := cutoffBoundaryComponents_card_le B H hH
    _ ≤ 8 * (3 * H) ^ 2 := by gcongr; omega
    _ = 72 * H ^ 2 := by ring

end Markov
