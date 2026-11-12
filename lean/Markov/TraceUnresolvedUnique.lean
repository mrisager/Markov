import Markov.TraceCutoffPathComponents
import Markov.TracePathArcOrder
import Markov.TraceCutoffNormalSeparation

/-! The paper's basic parameter assumption separates the actual cutoff
components' angular neighborhoods. Unresolved directions therefore have a
unique actual component, independent of its basepoint or signed labels. -/

noncomputable section
open Set
namespace Markov

/-- Distinct actual cutoff components have disjoint closed angular
neighborhoods under the paper's basic parameter assumption. -/
theorem traceUncutBoundary_angular_neighborhood_disjoint
    (H ε η : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength) * H))
    (x y : TracePlane) (hx : x ∈ traceUncutBoundary H) (hy : y ∈ traceUncutBoundary H)
    (hne : connectedComponentIn (traceUncutBoundary H) x ≠
      connectedComponentIn (traceUncutBoundary H) y) :
    Disjoint
      (closedAngularNeighborhood
        (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η)
      (closedAngularNeighborhood
        (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) y)) η) := by
  obtain ⟨a, b, ha, hab, hb, _, hbcut, hxarc⟩ :=
    traceUncutBoundary_exists_path_component H hH x hx
  obtain ⟨c, d, hc, hcd, hd, _, hdcut, hyarc⟩ :=
    traceUncutBoundary_exists_path_component H hH y hy
  have hnearc : traceBoundaryOpenArc a b ≠ traceBoundaryOpenArc c d := by
    simpa only [hxarc, hyarc] using hne
  obtain hbc | hda := traceBoundaryOpenArc_parameters_ordered_of_distinct_components
    (traceUncutBoundary H) x y a b c d hab hcd hxarc hyarc hnearc
  · rw [hxarc, hyarc]
    apply trace_ordered_cutoff_arcs_angular_neighborhood_disjoint H a b c d ε η
      ha hab hbc hcd hd hbcut hdcut hε hη
    simpa only [neg_mul, mul_assoc] using hbasic
  · rw [hxarc, hyarc]
    apply Disjoint.symm
    apply trace_ordered_cutoff_arcs_angular_neighborhood_disjoint H c d a b ε η
      hc hcd hda hab hb hdcut hbcut hε hη
    simpa only [neg_mul, mul_assoc] using hbasic

/-- Membership in the same angular neighborhood direction forces two
actual cutoff components to be equal. The basepoints need not agree. -/
theorem traceUncutBoundary_component_eq_of_neighborhood_membership
    (H ε η : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength) * H))
    (x y : TracePlane) (hx : x ∈ traceUncutBoundary H) (hy : y ∈ traceUncutBoundary H)
    (z : EuclideanSpace ℝ (Fin 2))
    (hz : z ∈ closedAngularNeighborhood
      (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η)
    (hz' : z ∈ closedAngularNeighborhood
      (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) y)) η) :
    connectedComponentIn (traceUncutBoundary H) x =
      connectedComponentIn (traceUncutBoundary H) y := by
  by_contra hne
  exact Set.disjoint_left.mp
    (traceUncutBoundary_angular_neighborhood_disjoint H ε η hH hε hη hbasic x y hx hy hne)
    hz hz'

/-- Every unresolved direction has exactly one associated actual
component under the paper's basic assumption. This does not assert
uniqueness of the signed sector or the component's basepoint. -/
theorem IsTraceUnresolved.unique_component
    {d : ℤ × ℤ} {K H η : ℝ} (h : IsTraceUnresolved d K H η)
    (ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) (hη : 0 < η)
    (hbasic : (2 + ε) * η ≤ traceCornerLowerConstant *
      Real.exp (-(2 * traceAxisLength) * H)) :
    ∃! Γ : Set TracePlane,
      (∃ x ∈ traceUncutBoundary H,
        connectedComponentIn (traceUncutBoundary H) x = Γ) ∧
      NormedSpace.normalize (euclideanIntDirection d) ∈
        closedAngularNeighborhood (normalsOn traceBasis Γ) η := by
  obtain ⟨_, _, x, hx, hz⟩ := h
  refine ⟨connectedComponentIn (traceUncutBoundary H) x, ⟨⟨x, hx, rfl⟩, hz⟩, ?_⟩
  rintro Γ ⟨⟨y, hy, rfl⟩, hz'⟩
  exact traceUncutBoundary_component_eq_of_neighborhood_membership
    H ε η hH hε hη hbasic y x hy hx _ hz' hz

end Markov
