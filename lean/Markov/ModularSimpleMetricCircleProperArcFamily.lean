import Markov.ModularSimpleMetricCircleNormalDiagramH1
import Markov.PaperAxisProperArcGluing

/-! The arbitrary actually embedded local-unit-speed metric circle gives an
actual finite family of PROPER original-Q arcs: all internal pieces plus ONE
joined wrap piece. The same actual word and genuine original H1 are retained.
No boundary endpoint ordering or simple-class classification is asserted. -/
noncomputable section
open Set Topology
namespace Markov

/-- An arbitrary supplied embedded metric circle yields a genuine finite
proper-Q arc family with closed embeddings, strict interiors, unique different
endpoint sides, pairwise disjoint open images and actual cyclic projected
gluing. All literal circle projections and same-word/H1 witnesses are retained. -/
theorem modularSimpleMetricCircle_proper_Q_arc_family
    (L : ℝ) (hL : 0 < L) (q : C(AddCircle L, ModularTraceQuotient))
    (hq : IsClosedEmbedding q)
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (q (s : AddCircle L)) (q (u : AddCircle L)) = dist s u) :
    ∃ (D : modularTraceSubgroup) (hg : 2 < |(D.val : IntMatrixTwo).trace|) (c a : ℝ)
      (hoff : a ∉ paperAxisSideCuts D hg),
      modularClosedGeodesicPeriod D = L ∧
      (∀ t : ℝ, q (t : AddCircle L) = modularClosedGeodesic D hg (t + c)) ∧
      a ∈ Ioo 0 (modularClosedGeodesicPeriod D) ∧
      a + modularClosedGeodesicPeriod D ∉ paperAxisSideCuts D hg ∧
      Fintype.card (paperAxisProperArcIndex D hg a) =
        (paperAxisPeriodCellWord D hg a).length ∧
      (∀ i : paperAxisProperArcIndex D hg a,
        IsClosedEmbedding (paperAxisProperArc D hg a hoff i)) ∧
      (∀ (i : paperAxisProperArcIndex D hg a) (s : unitInterval),
        0 < (s : ℝ) → (s : ℝ) < 1 →
        (paperAxisProperArc D hg a hoff i s : UpperHalfPlane) ∈
          paperIdealQuadrilateralStrictRegion) ∧
      (∀ i : paperAxisProperArcIndex D hg a,
        ∃ k l : Fin 4, k ≠ l ∧
          (paperAxisProperArc D hg a hoff i 0 : UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide k ∧
          (paperAxisProperArc D hg a hoff i 1 : UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide l ∧
          (∀ k', (paperAxisProperArc D hg a hoff i 0 : UpperHalfPlane) ∈
            paperQuadrilateralGeodesicSide k' → k' = k) ∧
          (∀ l', (paperAxisProperArc D hg a hoff i 1 : UpperHalfPlane) ∈
            paperQuadrilateralGeodesicSide l' → l' = l)) ∧
      (∀ (i j : paperAxisProperArcIndex D hg a), i ≠ j →
        Disjoint ((paperAxisProperArc D hg a hoff i) '' Ioo (0 : unitInterval) 1)
          ((paperAxisProperArc D hg a hoff j) '' Ioo (0 : unitInterval) 1)) ∧
      (∀ i : paperAxisProperArcIndex D hg a,
        modularTraceQuotientMk (paperAxisProperArc D hg a hoff i 1) =
          modularTraceQuotientMk (paperAxisProperArc D hg a hoff
            (paperAxisProperArcNextIndex D hg a i) 0)) ∧
      ((paperAxisPeriodCellWord D hg a).map paperQuadrilateralSideNeighbor).prod =
        (paperAxisPeriodGapCellLabel D hg a (paperAxisFirstGapIndex D hg a))⁻¹ *
          D * paperAxisPeriodGapCellLabel D hg a (paperAxisFirstGapIndex D hg a) ∧
      ((paperAxisPeriodCellWord D hg a).map paperAxisCellLetterCoordinates).sum =
        modularTraceFixedSingularH1Equiv
          (singularLoopClass ModularTraceQuotient (modularMetricCirclePositiveLoop L q)) ∧
      (∀ (i : paperAxisProperArcIndex D hg a) (s : unitInterval),
        modularTraceQuotientMk (paperAxisProperArc D hg a hoff i s) =
          q ((paperAxisProperArcParameter D hg a i s - c : ℝ) : AddCircle L)) := by
  obtain ⟨D, hg, c, a, hlen, hphase, ha, hoff, hendoff, hinj, _, _, _, _, hprod,
    _, hcoord⟩ := modularSimpleMetricCircle_finite_Q_itinerary_coordinates L hL q hq hloc
  refine ⟨D, hg, c, a, hoff, hlen, hphase, ha, hendoff,
    paperAxisProperArc_card D hg a,
    fun i => paperAxisProperArc_isClosedEmbedding D hg a hoff i,
    fun i s hs0 hs1 => paperAxisProperArc_strict D hg a hoff i s hs0 hs1,
    fun i => paperAxisProperArc_endpoint_sides D hg a hoff i,
    fun i j hij => paperAxisProperArc_interiors_disjoint D hg a hoff hinj i j hij,
    fun i => paperAxisProperArc_projected_gluing D hg a hoff i, hprod, hcoord, ?_⟩
  intro i s
  rw [paperAxisProperArc_project, hphase]
  simp only [sub_add_cancel]
  rfl

end Markov
