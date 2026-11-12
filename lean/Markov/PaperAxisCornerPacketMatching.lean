import Markov.PaperAxisCornerPacketIntervals
import Mathlib.Order.Interval.Finset.Fin

/-! Exact actual rank matching within each corner. The genuine ARC
involution bijects tags after a source with tags before its actual partner. -/
noncomputable section
open Set
namespace Markov

private def actualAboveRankEquiv
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card) :
    {j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card // i < j} ≃
    {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k ∧
      paperAxisProperEndpointBoundaryCoordinate g hg a ha
        (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) <
      paperAxisProperEndpointBoundaryCoordinate g hg a ha t} := by
  classical
  let f := fun j : {j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card // i < j} =>
    (⟨paperAxisProperEndpointBoundarySortedTag g hg a ha k j.val,
      ⟨paperAxisProperEndpointBoundarySortedTag_side g hg a ha k j.val,
        paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k j.property⟩⟩ :
      {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k ∧
        paperAxisProperEndpointBoundaryCoordinate g hg a ha
          (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) <
        paperAxisProperEndpointBoundaryCoordinate g hg a ha t})
  apply Equiv.ofBijective f
  constructor
  · intro j l he
    apply Subtype.ext
    apply (paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k).injective
    exact congrArg (paperAxisProperEndpointBoundaryCoordinate g hg a ha)
      (congrArg Subtype.val he)
  · intro t
    have hr : t.val ∈ Set.range (paperAxisProperEndpointBoundarySortedTag g hg a ha k) := by
      rw [paperAxisProperEndpointBoundarySortedTag_range g hg a ha hproject k]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,t.property.1⟩
    obtain ⟨j,hj⟩ := hr
    have hlt : i < j := (paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k).lt_iff_lt.mp
      (by simpa only [hj] using t.property.2)
    exact ⟨⟨j,hlt⟩, Subtype.ext hj⟩

private def actualBelowRankEquiv
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card) :
    {j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card // j < i} ≃
    {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k ∧
      paperAxisProperEndpointBoundaryCoordinate g hg a ha t <
      paperAxisProperEndpointBoundaryCoordinate g hg a ha
        (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)} := by
  classical
  let f := fun j : {j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card // j < i} =>
    (⟨paperAxisProperEndpointBoundarySortedTag g hg a ha k j.val,
      ⟨paperAxisProperEndpointBoundarySortedTag_side g hg a ha k j.val,
        paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k j.property⟩⟩ :
      {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k ∧
        paperAxisProperEndpointBoundaryCoordinate g hg a ha t <
        paperAxisProperEndpointBoundaryCoordinate g hg a ha
          (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)})
  apply Equiv.ofBijective f
  constructor
  · intro j l he
    apply Subtype.ext
    apply (paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k).injective
    exact congrArg (paperAxisProperEndpointBoundaryCoordinate g hg a ha)
      (congrArg Subtype.val he)
  · intro t
    have hr : t.val ∈ Set.range (paperAxisProperEndpointBoundarySortedTag g hg a ha k) := by
      rw [paperAxisProperEndpointBoundarySortedTag_range g hg a ha hproject k]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,t.property.1⟩
    obtain ⟨j,hj⟩ := hr
    have hlt : j < i := (paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k).lt_iff_lt.mp
      (by simpa only [hj] using t.property.2)
    exact ⟨⟨j,hlt⟩, Subtype.ext hj⟩

private theorem actualAboveRankCard
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card) :
    Fintype.card {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k ∧
      paperAxisProperEndpointBoundaryCoordinate g hg a ha
        (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) <
      paperAxisProperEndpointBoundaryCoordinate g hg a ha t} =
      (paperAxisProperEndpointSideCoordinates g hg a ha k).card - 1 - i.val := by
  classical
  rw [← Fintype.card_congr (actualAboveRankEquiv g hg a ha hproject k i)]
  rw [Fintype.card_of_subtype (Finset.Ioi i) (fun _ => Finset.mem_Ioi), Fin.card_Ioi]

private theorem actualBelowRankCard
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card) :
    Fintype.card {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k ∧
      paperAxisProperEndpointBoundaryCoordinate g hg a ha t <
      paperAxisProperEndpointBoundaryCoordinate g hg a ha
        (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)} = i.val := by
  classical
  rw [← Fintype.card_congr (actualBelowRankEquiv g hg a ha hproject k i)]
  rw [Fintype.card_of_subtype (Finset.Iio i) (fun _ => Finset.mem_Iio), Fin.card_Iio]

/-- Every actual corner arc matches source rank i with next-side rank j
according to i+j+1=N_source. The actual ARC bijection between all later source
tags and all earlier target tags proves the offset, including full cardinality. -/
theorem paperAxisCorner_actual_partner_rank_sum
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide k)).card)
    (hpair : paperAxisProperArcEndpointPair g hg a
      (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) =
      paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralNextSide k) j) :
    i.val + j.val + 1 = (paperAxisProperEndpointSideCoordinates g hg a ha k).card := by
  classical
  have hs := paperAxisProperEndpointBoundarySortedTag_side g hg a ha k i
  have hp : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a
      (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) = paperQuadrilateralNextSide k := by
    rw [hpair]
    exact paperAxisProperEndpointBoundarySortedTag_side g hg a ha (paperQuadrilateralNextSide k) j
  let E :
      {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k ∧
        paperAxisProperEndpointBoundaryCoordinate g hg a ha
          (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) <
        paperAxisProperEndpointBoundaryCoordinate g hg a ha t} ≃
      {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = paperQuadrilateralNextSide k ∧
        paperAxisProperEndpointBoundaryCoordinate g hg a ha t <
        paperAxisProperEndpointBoundaryCoordinate g hg a ha
          (paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralNextSide k) j)} :=
    Equiv.subtypeEquiv (paperAxisProperArcEndpointPair g hg a) (by
      intro t
      constructor
      · rintro ⟨ht,hlt⟩
        have hn := paperAxisCorner_source_nearer_partner g hg a ha hproject k _ t hs hp ht hlt
        exact ⟨hn.1, by simpa only [hpair] using hn.2⟩
      · rintro ⟨ht,hlt⟩
        have hl : paperAxisProperEndpointBoundaryCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a t) <
            paperAxisProperEndpointBoundaryCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a
              (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) := by
          simpa only [hpair] using hlt
        have hn := paperAxisCorner_next_nearer_partner g hg a ha hproject k _
          (paperAxisProperArcEndpointPair g hg a t) hs hp ht hl
        rw [paperAxisProperArcEndpointPair_involutive g hg a t] at hn
        exact hn)
  have hc := Fintype.card_congr E
  rw [actualAboveRankCard g hg a ha hproject k i,
    actualBelowRankCard g hg a ha hproject (paperQuadrilateralNextSide k) j] at hc
  have hi := i.isLt
  omega

/-- The literal next-side partner exists in its actual sorted list and has
the forced rank offset. No partner-rank formula is supplied as a hypothesis. -/
theorem paperAxisNextCornerPacket_actual_partner_offset
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (hi : paperAxisNextCornerPacketStart g hg a ha k ≤ i.val) :
    ∃ j : Fin (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide k)).card,
      paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) =
        paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralNextSide k) j ∧
      j.val = (paperAxisProperEndpointSideCoordinates g hg a ha k).card - 1 - i.val := by
  classical
  have hp := (paperAxisNextCornerPacket_iff_start_le g hg a ha hproject k i).mpr hi
  have hr : paperAxisProperArcEndpointPair g hg a (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) ∈
      Set.range (paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralNextSide k)) := by
    rw [paperAxisProperEndpointBoundarySortedTag_range g hg a ha hproject (paperQuadrilateralNextSide k)]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
  obtain ⟨j,hj⟩ := hr
  have he := paperAxisCorner_actual_partner_rank_sum g hg a ha hproject k i j hj.symm
  refine ⟨j,hj.symm,?_⟩
  omega

end Markov
