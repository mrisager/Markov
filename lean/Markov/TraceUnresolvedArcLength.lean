import Markov.TraceUnresolvedSizes
import Markov.TraceUnresolvedUnique

/-! A concrete choice of the actual unresolved component and its finite
Euclidean radial curve variation.  Values outside the unresolved regime at
height at least one are set to zero.  The construction uses the trace unit
boundary and makes no identification with a geometric hyperbolic ball. -/

noncomputable section
open Set
namespace Markov

/-- Data for an actual unresolved component, including its exact signed
radial parametrization and the original angular-neighborhood membership. -/
structure TraceUnresolvedComponentData (d : ℤ × ℤ) (H η : ℝ) where
  basepoint : TracePlane
  mem_uncut : basepoint ∈ traceUncutBoundary H
  sector : Fin 8
  left : ℤ × ℤ
  right : ℤ × ℤ
  consecutive : ConsecutiveCutoffSlopes ⌊H⌋₊ left right
  component_eq : connectedComponentIn (traceUncutBoundary H) basepoint =
    slopeBoundaryArc (signedSectorBasis traceBasis sector)
      (cutoffSlope left) (cutoffSlope right)
  neighborhood_mem : NormedSpace.normalize (euclideanIntDirection d) ∈
    closedAngularNeighborhood (normalsOn traceBasis
      (slopeBoundaryArc (signedSectorBasis traceBasis sector)
        (cutoffSlope left) (cutoffSlope right))) η

/-- Existence of signed data for an actual unresolved component. -/
theorem IsTraceUnresolved.component_data_nonempty
    {d : ℤ × ℤ} {K H η : ℝ} (h : IsTraceUnresolved d K H η) (hH : 1 ≤ H) :
    Nonempty (TraceUnresolvedComponentData d H η) := by
  obtain ⟨x, hx, k, u, v, hconsecutive, _, hcomp, hmem⟩ :=
    h.exists_signed_cutoff_component hH
  exact ⟨⟨x, hx, k, u, v, hconsecutive, hcomp, hmem⟩⟩

/-- A chosen actual unresolved component, independent of the later
auxiliary parameter ε used in the size estimates. -/
def traceUnresolvedComponentData (d : ℤ × ℤ) (K H η : ℝ)
    (h : IsTraceUnresolved d K H η ∧ 1 ≤ H) : TraceUnresolvedComponentData d H η :=
  Classical.choice (h.1.component_data_nonempty h.2)

/-- Euclidean radial variation of the chosen actual unresolved component.
The fallback outside the stated regime is zero. -/
def traceUnresolvedArcLength (d : ℤ × ℤ) (K H η : ℝ) : ℝ := by
  classical
  exact if h : IsTraceUnresolved d K H η ∧ 1 ≤ H then
    let a := traceUnresolvedComponentData d K H η h
    (signedTraceCutoffArcLength a.sector a.left a.right).toReal
  else 0

/-- The chosen actual component as a subset of the trace unit boundary. -/
def traceUnresolvedComponent (d : ℤ × ℤ) (K H η : ℝ) : Set TracePlane := by
  classical
  exact if h : IsTraceUnresolved d K H η ∧ 1 ≤ H then
    let a := traceUnresolvedComponentData d K H η h
    slopeBoundaryArc (signedSectorBasis traceBasis a.sector)
      (cutoffSlope a.left) (cutoffSlope a.right)
  else ∅

theorem traceUnresolvedArcLength_nonneg (d : ℤ × ℤ) (K H η : ℝ) :
    0 ≤ traceUnresolvedArcLength d K H η := by
  classical
  unfold traceUnresolvedArcLength
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

/-- Under the unresolved hypotheses the selected scalar is the actual
signed radial variation, and its component has an uncut basepoint. -/
theorem traceUnresolvedArcLength_spec
    (d : ℤ × ℤ) (K H η : ℝ) (h : IsTraceUnresolved d K H η) (hH : 1 ≤ H) :
    ∃ x ∈ traceUncutBoundary H, ∃ (k : Fin 8) (u v : ℤ × ℤ),
      ConsecutiveCutoffSlopes ⌊H⌋₊ u v ∧
      connectedComponentIn (traceUncutBoundary H) x =
        traceUnresolvedComponent d K H η ∧
      traceUnresolvedComponent d K H η =
        slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) ∧
      NormedSpace.normalize (euclideanIntDirection d) ∈
        closedAngularNeighborhood (normalsOn traceBasis
          (traceUnresolvedComponent d K H η)) η ∧
      signedTraceCutoffArcLength k u v ≠ ⊤ ∧
      traceUnresolvedArcLength d K H η =
        (signedTraceCutoffArcLength k u v).toReal := by
  let a := traceUnresolvedComponentData d K H η ⟨h, hH⟩
  have hcomp : traceUnresolvedComponent d K H η =
      slopeBoundaryArc (signedSectorBasis traceBasis a.sector)
        (cutoffSlope a.left) (cutoffSlope a.right) := by
    simp only [traceUnresolvedComponent, dif_pos (show IsTraceUnresolved d K H η ∧ 1 ≤ H
      from ⟨h, hH⟩)]
    rfl
  have hlength : traceUnresolvedArcLength d K H η =
      (signedTraceCutoffArcLength a.sector a.left a.right).toReal := by
    simp only [traceUnresolvedArcLength, dif_pos (show IsTraceUnresolved d K H η ∧ 1 ≤ H
      from ⟨h, hH⟩)]
    rfl
  refine ⟨a.basepoint, a.mem_uncut, a.sector, a.left, a.right, a.consecutive,
    a.component_eq.trans hcomp.symm, hcomp, ?_, ?_, hlength⟩
  · rw [hcomp]
    exact a.neighborhood_mem
  · exact ne_top_of_le_ne_top (by finiteness)
      (signedTraceCutoffArcLength_le_original_heights
        a.sector ⌊H⌋₊ a.left a.right a.consecutive)

/-- The chosen variation is a finite radial curve variation on a closed
parameter interval describing the actual unresolved component. -/
theorem traceUnresolvedArcLength_eq_finite_variation
    (d : ℤ × ℤ) (K H η : ℝ) (h : IsTraceUnresolved d K H η) (hH : 1 ≤ H) :
    ∃ (k : Fin 8) (u v : ℤ × ℤ),
      ConsecutiveCutoffSlopes ⌊H⌋₊ u v ∧
      traceUnresolvedComponent d K H η =
        slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) ∧
      eVariationOn (signedTraceEuclideanRadialSection k)
        (Icc (cutoffSlope u) (cutoffSlope v)) ≠ ⊤ ∧
      traceUnresolvedArcLength d K H η =
        (eVariationOn (signedTraceEuclideanRadialSection k)
          (Icc (cutoffSlope u) (cutoffSlope v))).toReal := by
  obtain ⟨_, _, k, u, v, hconsecutive, _, hcomp, _, hfinite, hlength⟩ :=
    traceUnresolvedArcLength_spec d K H η h hH
  exact ⟨k, u, v, hconsecutive, hcomp, hfinite, hlength⟩

/-- A single positive constant controls the chosen actual Euclidean
variation for all unresolved directions and all admissible parameters. -/
theorem exists_traceUnresolvedArcLength_bound :
    ∃ Ca : ℝ, 0 < Ca ∧
      ∀ (K H ε η : ℝ) (d : ℤ × ℤ), 1 ≤ H → 0 < ε →
        (2 + ε) * η ≤ traceCornerLowerConstant *
          Real.exp (-(2 * traceAxisLength) * H) →
        IsTraceUnresolved d K H η →
        traceUnresolvedArcLength d K H η ≤
          Ca * Real.sqrt (intEuclidean d) / (H * Real.sqrt H) := by
  obtain ⟨_, Ca, _, hCa, hbound⟩ :=
    real_cutoff_signed_unresolved_height_and_arc_bound
  refine ⟨Ca, hCa, ?_⟩
  intro K H ε η d hH hε hbasic h
  obtain ⟨_, _, k, u, v, hconsecutive, _, hcomp, hmem, _, hlength⟩ :=
    traceUnresolvedArcLength_spec d K H η h hH
  rw [hcomp] at hmem
  rw [hlength]
  exact (hbound H ε η hH hε hbasic k u v d hconsecutive h.1 hmem).2

/-- Under the basic parameter assumption the chosen actual component
agrees with every actual component having the required neighborhood
membership.  Signed labels and basepoints need not be unique. -/
theorem traceUnresolvedComponent_eq_actual_component
    (d : ℤ × ℤ) (K H ε η : ℝ) (h : IsTraceUnresolved d K H η)
    (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength) * H))
    (y : TracePlane) (hy : y ∈ traceUncutBoundary H)
    (hmem : NormedSpace.normalize (euclideanIntDirection d) ∈
      closedAngularNeighborhood
        (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) y)) η) :
    traceUnresolvedComponent d K H η =
      connectedComponentIn (traceUncutBoundary H) y := by
  obtain ⟨x, hx, _, _, _, _, hcomp, _, hz, _, _⟩ :=
    traceUnresolvedArcLength_spec d K H η h hH
  rw [← hcomp] at hz ⊢
  exact traceUncutBoundary_component_eq_of_neighborhood_membership
    H ε η hH hε hη hbasic x y hx hy _ hz hmem

end Markov
