import Markov.ModularSimpleMetricCircleNormalDiagram
import Markov.ModularMetricCircleCellWordH1

/-! The actual finite-Q construction for an arbitrary supplied embedded local
unit-speed metric circle retains its genuine original fixed-I singular H1.
The nonabelian word is constructed geometrically, never inferred from H1. -/
noncomputable section
open Set Topology
namespace Markov

/-- Every constructed actual normal-gap piece, literal cyclic deck word and
its genuine original signed H1 coordinates come from the same actual metric
circle and the same actual deck/axis/cut-table witnesses. -/
theorem modularSimpleMetricCircle_finite_Q_itinerary_coordinates
    (L : ℝ) (hL : 0 < L) (q : C(AddCircle L, ModularTraceQuotient))
    (hq : IsClosedEmbedding q)
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (q (s : AddCircle L)) (q (u : AddCircle L)) = dist s u) :
    ∃ (D : modularTraceSubgroup) (hg : 2 < |(D.val : IntMatrixTwo).trace|) (c a : ℝ),
      modularClosedGeodesicPeriod D = L ∧
      (∀ t : ℝ, q (t : AddCircle L) = modularClosedGeodesic D hg (t + c)) ∧
      a ∈ Ioo 0 (modularClosedGeodesicPeriod D) ∧
      a ∉ paperAxisSideCuts D hg ∧
      a + modularClosedGeodesicPeriod D ∉ paperAxisSideCuts D hg ∧
      (∀ b : ℝ, Set.InjOn (fun t : ℝ =>
        modularTraceQuotientMk (modularHyperbolicAxis D hg t))
        (Ioo b (b + modularClosedGeodesicPeriod D))) ∧
      (∀ i : Fin ((paperAxisPeriodCutPoints D hg a).card - 1),
        IsClosedEmbedding (paperAxisPeriodGapSubarc D hg a i)) ∧
      (∀ (i : Fin ((paperAxisPeriodCutPoints D hg a).card - 1)) (s : unitInterval),
        0 < (s : ℝ) → (s : ℝ) < 1 →
        (paperAxisPeriodGapSubarc D hg a i s : UpperHalfPlane) ∈
          paperIdealQuadrilateralStrictRegion) ∧
      (∀ (i j : Fin ((paperAxisPeriodCutPoints D hg a).card - 1)), i ≠ j →
        Disjoint ((paperAxisPeriodGapSubarc D hg a i) '' Ioo (0 : unitInterval) 1)
          ((paperAxisPeriodGapSubarc D hg a j) '' Ioo (0 : unitInterval) 1)) ∧
      (∀ (i : Fin ((paperAxisPeriodCutPoints D hg a).card - 1)),
        0 < i.val → i.val + 2 < (paperAxisPeriodCutPoints D hg a).card →
        ∃ k l : Fin 4, k ≠ l ∧
          (paperAxisPeriodGapSubarc D hg a i 0 : UpperHalfPlane) ∈
            paperQuadrilateralGeodesicSide k ∧
          (paperAxisPeriodGapSubarc D hg a i 1 : UpperHalfPlane) ∈
            paperQuadrilateralGeodesicSide l) ∧
      ((paperAxisPeriodCellWord D hg a).map paperQuadrilateralSideNeighbor).prod =
        (paperAxisPeriodGapCellLabel D hg a (paperAxisFirstGapIndex D hg a))⁻¹ *
          D * paperAxisPeriodGapCellLabel D hg a (paperAxisFirstGapIndex D hg a) ∧
      (∀ (i : Fin ((paperAxisPeriodCutPoints D hg a).card - 1)) (s : unitInterval),
        modularTraceQuotientMk (paperAxisPeriodGapSubarc D hg a i s) =
          q ((paperAxisPeriodGapParameter D hg a i s - c : ℝ) : AddCircle L)) ∧
      ((paperAxisPeriodCellWord D hg a).map paperAxisCellLetterCoordinates).sum =
        modularTraceFixedSingularH1Equiv
          (singularLoopClass ModularTraceQuotient (modularMetricCirclePositiveLoop L q)) := by
  obtain ⟨D, hg, c, a, hlen, hphase, ha, hoff, hendoff, hinj, hemb, hstrict,
    hdisj, hsides, hprod, hproj⟩ :=
    modularSimpleMetricCircle_finite_Q_itinerary L hL q hq hloc
  refine ⟨D, hg, c, a, hlen, hphase, ha, hoff, hendoff, hinj, hemb, hstrict,
    hdisj, hsides, hprod, hproj, ?_⟩
  exact (modularMetricCircle_positiveLoop_cellWord_coordinates_of_axis_phase
    L q D hg c hlen hphase a hoff).symm

end Markov
