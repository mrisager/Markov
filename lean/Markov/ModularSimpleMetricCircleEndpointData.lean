import Markov.PaperAxisProperEndpointOrderPairing
import Markov.ModularSimpleMetricCircleNormalDiagramH1

/-! The actual finite tagged, sorted and paired endpoint data are constructed
from an arbitrary supplied embedded locally unit-speed metric circle. No
normal-diagram ordering, matching, layer or classification fields are inputs. -/
noncomputable section
open Set Topology
namespace Markov

/-- Arc-paired actual endpoints lie on different literal original sides,
derived from the actual unique different-side endpoint theorem. -/
theorem paperAxisProperArcEndpointPair_sides_ne (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a) :
    paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) ≠
      paperAxisProperEndpointSide g hg a ha t := by
  rcases t with ⟨i,e⟩
  obtain ⟨k,l,hkl,hk,hl,_,_⟩ := paperAxisProperArc_endpoint_sides g hg a ha i
  have h0 : paperAxisProperEndpointSide g hg a ha (i,0) = k :=
    (paperAxisProperEndpointSide_unique g hg a ha (i,0) k hk).symm
  have h1 : paperAxisProperEndpointSide g hg a ha (i,1) = l :=
    (paperAxisProperEndpointSide_unique g hg a ha (i,1) l hl).symm
  fin_cases e
  · change paperAxisProperEndpointSide g hg a ha (i,1) ≠
      paperAxisProperEndpointSide g hg a ha (i,0)
    rw [h1,h0]
    exact hkl.symm
  · change paperAxisProperEndpointSide g hg a ha (i,0) ≠
      paperAxisProperEndpointSide g hg a ha (i,1)
    rw [h0,h1]
    exact hkl

/-- Actual normalization, closed-arc separation, literal side-chart sorting,
and actual geometric cyclic gluing construct tagged/sorted/paired endpoints
for the SAME actual deck/phase/word/H1 witnesses of the supplied metric circle. -/
theorem modularSimpleMetricCircle_tagged_sorted_paired_endpoint_data
    (L : ℝ) (hL : 0 < L) (q : C(AddCircle L, ModularTraceQuotient))
    (hq : IsClosedEmbedding q)
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (q (s : AddCircle L)) (q (u : AddCircle L)) = dist s u) :
    ∃ (D : modularTraceSubgroup) (hg : 2 < |(D.val : IntMatrixTwo).trace|) (c a : ℝ)
      (hoff : a ∉ paperAxisSideCuts D hg),
      modularClosedGeodesicPeriod D = L ∧
      (∀ t : ℝ, q (t : AddCircle L) = modularClosedGeodesic D hg (t+c)) ∧
      (∀ b : ℝ, Set.InjOn (fun r : ℝ =>
        modularTraceQuotientMk (modularHyperbolicAxis D hg r))
        (Ioo b (b+modularClosedGeodesicPeriod D))) ∧
      Function.Injective (paperAxisProperEndpointPoint D hg a hoff) ∧
      Fintype.card (paperAxisProperEndpointTag D hg a) =
        2 * (paperAxisPeriodCellWord D hg a).length ∧
      (∀ k : Fin 4,
        (paperAxisProperEndpointSideCoordinates D hg a hoff k).card =
          (paperAxisProperEndpointSideTags D hg a hoff k).card ∧
        StrictMono (fun i => paperAxisProperEndpointCoordinate D hg a hoff
          (paperAxisProperEndpointSortedTag D hg a hoff k i)) ∧
        Set.range (paperAxisProperEndpointSortedTag D hg a hoff k) =
          (paperAxisProperEndpointSideTags D hg a hoff k : Set (paperAxisProperEndpointTag D hg a))) ∧
      Function.Involutive (paperAxisProperArcEndpointPair D hg a) ∧
      Function.Involutive (paperAxisProperEdgePair D hg a) ∧
      (∀ t : paperAxisProperEndpointTag D hg a,
        paperAxisProperArcEndpointPair D hg a t ≠ t ∧
        paperAxisProperEdgePair D hg a t ≠ t ∧
        paperAxisProperEndpointSide D hg a hoff (paperAxisProperArcEndpointPair D hg a t) ≠
          paperAxisProperEndpointSide D hg a hoff t ∧
        paperAxisProperEndpointSide D hg a hoff (paperAxisProperEdgePair D hg a t) =
          paperQuadrilateralOppositeSide (paperAxisProperEndpointSide D hg a hoff t) ∧
        paperAxisProperEndpointCoordinate D hg a hoff t =
          paperAxisProperEndpointCoordinate D hg a hoff (paperAxisProperEdgePair D hg a t) ∧
        modularTraceQuotientMk (paperAxisProperEndpointPoint D hg a hoff t) =
          modularTraceQuotientMk (paperAxisProperEndpointPoint D hg a hoff
            (paperAxisProperEdgePair D hg a t))) ∧
      (∀ k : Fin 4, paperAxisProperEndpointSideCount D hg a hoff k =
        paperAxisProperEndpointSideCount D hg a hoff (paperQuadrilateralOppositeSide k)) ∧
      ((paperAxisPeriodCellWord D hg a).map paperQuadrilateralSideNeighbor).prod =
        (paperAxisPeriodGapCellLabel D hg a (paperAxisFirstGapIndex D hg a))⁻¹ *
          D * paperAxisPeriodGapCellLabel D hg a (paperAxisFirstGapIndex D hg a) ∧
      ((paperAxisPeriodCellWord D hg a).map paperAxisCellLetterCoordinates).sum =
        modularTraceFixedSingularH1Equiv
          (singularLoopClass ModularTraceQuotient (modularMetricCirclePositiveLoop L q)) ∧
      (∀ t : paperAxisProperEndpointTag D hg a,
        modularTraceQuotientMk (paperAxisProperEndpointPoint D hg a hoff t) =
          q ((paperAxisProperArcParameter D hg a t.1 (paperAxisProperEndpointParameter t.2)-c : ℝ) :
            AddCircle L)) := by
  obtain ⟨D,hg,c,a,hlen,hphase,_,hoff,_,hinj,_,_,_,_,hprod,_,hcoord⟩ :=
    modularSimpleMetricCircle_finite_Q_itinerary_coordinates L hL q hq hloc
  refine ⟨D,hg,c,a,hoff,hlen,hphase,hinj,
    paperAxisProperEndpointPoint_injective D hg a hoff hinj,
    paperAxisProperEndpointTag_card D hg a, ?_,
    paperAxisProperArcEndpointPair_involutive D hg a,
    paperAxisProperEdgePair_involutive D hg a, ?_,
    fun k => paperAxisProperEndpointSideCount_eq_opposite D hg a hoff hinj k,
    hprod,hcoord,?_⟩
  · intro k
    exact ⟨paperAxisProperEndpointSideCoordinates_card D hg a hoff hinj k,
      paperAxisProperEndpointSortedTag_strictMono D hg a hoff k,
      paperAxisProperEndpointSortedTag_range D hg a hoff hinj k⟩
  · intro t
    have he := paperAxisProperEdgePair_opposite_and_coordinate D hg a hoff hinj t
    exact ⟨paperAxisProperArcEndpointPair_ne D hg a t,
      paperAxisProperEdgePair_ne D hg a t,
      paperAxisProperArcEndpointPair_sides_ne D hg a hoff t,
      he.1,he.2,paperAxisProperEdgePair_project D hg a hoff t⟩
  · intro t
    change modularTraceQuotientMk (paperAxisProperArc D hg a hoff t.1
      (paperAxisProperEndpointParameter t.2)) = _
    rw [paperAxisProperArc_project,hphase]
    simp only [sub_add_cancel]
    rfl

end Markov
