import Markov.ModularSimpleMetricCircleNormalization
import Markov.IntegerPeriodOpenIntervalInjectivity
import Markov.PaperAxisNormalArcEndpoints
import Markov.PaperAxisOrderedCellWord

/-! Actual finite original-Q gap pieces and an actual ordered side word for
any supplied closed embedded locally unit-speed metric circle. The first and
last pieces are cut at the chosen off-side period base; only internal pieces
are asserted to have two boundary endpoints. No class premise is used. -/
noncomputable section
open Set Topology
namespace Markov

/-- The actual metric-circle lift normalization supplies the actual finite-Q
table, closed embedded gap pieces with disjoint open images, genuine internal
normal-arc endpoints, and the literal nonabelian period word. Every piece
projects to the supplied circle at its displayed real parameter and phase. -/
theorem modularSimpleMetricCircle_finite_Q_itinerary
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
          q ((paperAxisPeriodGapParameter D hg a i s - c : ℝ) : AddCircle L)) := by
  obtain ⟨D, hg, c, hlen, hphase, heq⟩ :=
    modularSimpleMetricCircle_axis_normalization L hL q hq hloc
  obtain ⟨a, ha, hoff, hendoff⟩ := paperAxisSideCuts_exists_period_base_off D hg
  have hinj (b : ℝ) : Set.InjOn (fun t : ℝ =>
      modularTraceQuotientMk (modularHyperbolicAxis D hg t))
      (Ioo b (b + modularClosedGeodesicPeriod D)) :=
    integerPeriodEquality_injOn_Ioo (modularClosedGeodesicPeriod D)
      (modularClosedGeodesicPeriod_pos D hg) (modularClosedGeodesic D hg) heq b
  refine ⟨D, hg, c, a, hlen, hphase, ha, hoff, hendoff, hinj,
    fun i => paperAxisPeriodGapSubarc_isClosedEmbedding D hg a i,
    fun i s hs0 hs1 => paperAxisPeriodGapSubarc_strict D hg a i s hs0 hs1,
    fun i j hij => paperAxisPeriodGapSubarc_interiors_disjoint_of_projected_period_injective
      D hg a (hinj a) i j hij, ?_, paperAxisPeriodCellWord_prod D hg a hoff, ?_⟩
  · intro i hfirst hlast
    obtain ⟨k, l, hkl, hk, hl, _, _⟩ :=
      paperAxisPeriodGapSubarc_internal_endpoint_sides D hg a i hfirst hlast
    exact ⟨k, l, hkl, hk, hl⟩
  · intro i s
    rw [paperAxisPeriodGapSubarc_project, hphase]
    simp only [sub_add_cancel]
    rfl

end Markov
