import Markov.PaperQuadrilateralBoundaryOrientation
import Markov.PaperAxisProperEndpointOrderPairing

/-! Actual boundary-oriented side ranks and actual rank lookup of the genuine
ARC pairing. No corner-packet contiguity or nearest-corner pairing is assumed. -/
noncomputable section
open Set
namespace Markov

/-- The actual oriented coordinate of each genuine tagged boundary point. -/
def paperAxisProperEndpointBoundaryCoordinate (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a) : ℝ :=
  paperQuadrilateralBoundarySideCoordinate (paperAxisProperEndpointSide g hg a ha t)
    (paperAxisProperEndpointPoint g hg a ha t)

/-- Actual chosen boundary order uses the constructed finite side sort,
with ranks reversed exactly on RIGHT and BOTTOM. -/
def paperAxisProperEndpointBoundarySortedTag (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card) :
    paperAxisProperEndpointTag g hg a :=
  paperAxisProperEndpointSortedTag g hg a ha k (if k = 1 ∨ k = 2 then i.rev else i)

/-- Every actual oriented-rank endpoint lies on its requested literal side. -/
theorem paperAxisProperEndpointBoundarySortedTag_side (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card) :
    paperAxisProperEndpointSide g hg a ha (paperAxisProperEndpointBoundarySortedTag g hg a ha k i) = k := by
  classical
  exact (Finset.mem_filter.mp (paperAxisProperEndpointSortedTag_spec
    g hg a ha k (if k = 1 ∨ k = 2 then i.rev else i)).1).2

private theorem boundaryCoordinate_sign (k : Fin 4) (z : paperIdealQuadrilateral) :
    paperQuadrilateralBoundarySideCoordinate k z =
      if k = 1 ∨ k = 2 then -paperQuadrilateralMarkedSideCoordinate k z
      else paperQuadrilateralMarkedSideCoordinate k z := by
  fin_cases k <;> rfl

private theorem boundaryCoordinate_on_side (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4)
    (t : paperAxisProperEndpointTag g hg a) (ht : paperAxisProperEndpointSide g hg a ha t = k) :
    paperAxisProperEndpointBoundaryCoordinate g hg a ha t =
      if k = 1 ∨ k = 2 then -paperAxisProperEndpointCoordinate g hg a ha t
      else paperAxisProperEndpointCoordinate g hg a ha t := by
  unfold paperAxisProperEndpointBoundaryCoordinate paperAxisProperEndpointCoordinate
  rw [ht, boundaryCoordinate_sign]

/-- The actual oriented side lists are strictly increasing in the chosen
+x,-y,-x,+y directions, without an assumed boundary-order field. -/
theorem paperAxisProperEndpointBoundarySortedTag_strictMono (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) :
    StrictMono (fun i => paperAxisProperEndpointBoundaryCoordinate g hg a ha
      (paperAxisProperEndpointBoundarySortedTag g hg a ha k i)) := by
  intro i j hij
  dsimp only
  rw [boundaryCoordinate_on_side _ _ _ _ k _ (paperAxisProperEndpointBoundarySortedTag_side _ _ _ _ k i),
    boundaryCoordinate_on_side _ _ _ _ k _ (paperAxisProperEndpointBoundarySortedTag_side _ _ _ _ k j)]
  by_cases hk : k = 1 ∨ k = 2
  · simp only [if_pos hk, paperAxisProperEndpointBoundarySortedTag]
    exact neg_lt_neg (paperAxisProperEndpointSortedTag_strictMono g hg a ha k
      (Fin.rev_lt_rev.mpr hij))
  · simp only [if_neg hk, paperAxisProperEndpointBoundarySortedTag]
    exact paperAxisProperEndpointSortedTag_strictMono g hg a ha k hij

/-- Oriented sorting still lists precisely all actual endpoint tags on the side. -/
theorem paperAxisProperEndpointBoundarySortedTag_range
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4) :
    Set.range (paperAxisProperEndpointBoundarySortedTag g hg a ha k) =
      (paperAxisProperEndpointSideTags g hg a ha k : Set (paperAxisProperEndpointTag g hg a)) := by
  classical
  ext t
  constructor
  · rintro ⟨i,rfl⟩
    exact (paperAxisProperEndpointSortedTag_spec g hg a ha k
      (if k = 1 ∨ k = 2 then i.rev else i)).1
  · intro ht
    have hr : t ∈ Set.range (paperAxisProperEndpointSortedTag g hg a ha k) := by
      rw [paperAxisProperEndpointSortedTag_range g hg a ha hproject k]
      exact ht
    obtain ⟨i,hi⟩ := hr
    by_cases hk : k = 1 ∨ k = 2
    · exact ⟨i.rev, by simpa only [paperAxisProperEndpointBoundarySortedTag, if_pos hk, Fin.rev_rev] using hi⟩
    · exact ⟨i, by simpa only [paperAxisProperEndpointBoundarySortedTag, if_neg hk] using hi⟩

private theorem endpointRank_exists
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (t : paperAxisProperEndpointTag g hg a) :
    ∃ i, paperAxisProperEndpointBoundarySortedTag g hg a ha
      (paperAxisProperEndpointSide g hg a ha t) i = t := by
  classical
  have ht : t ∈ paperAxisProperEndpointSideTags g hg a ha (paperAxisProperEndpointSide g hg a ha t) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  have hr : t ∈ Set.range (paperAxisProperEndpointBoundarySortedTag g hg a ha
      (paperAxisProperEndpointSide g hg a ha t)) := by
    rw [paperAxisProperEndpointBoundarySortedTag_range g hg a ha hproject]
    exact ht
  exact hr

/-- Actual oriented side rank of a genuine endpoint, obtained from its actual
complete sorted side list rather than supplied as a packet/rank field. -/
def paperAxisProperEndpointBoundaryRank
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (t : paperAxisProperEndpointTag g hg a) :
    Fin (paperAxisProperEndpointSideCoordinates g hg a ha (paperAxisProperEndpointSide g hg a ha t)).card :=
  (endpointRank_exists g hg a ha hproject t).choose

/-- Actual rank lookup recovers exactly the original genuine endpoint tag. -/
theorem paperAxisProperEndpointBoundaryRank_spec
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (t : paperAxisProperEndpointTag g hg a) :
    paperAxisProperEndpointBoundarySortedTag g hg a ha (paperAxisProperEndpointSide g hg a ha t)
      (paperAxisProperEndpointBoundaryRank g hg a ha hproject t) = t :=
  (endpointRank_exists g hg a ha hproject t).choose_spec

/-- Actual oriented rank of the other endpoint of the same genuine proper arc. -/
def paperAxisProperArcPartnerBoundaryRank
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (t : paperAxisProperEndpointTag g hg a) :=
  paperAxisProperEndpointBoundaryRank g hg a ha hproject (paperAxisProperArcEndpointPair g hg a t)

/-- The computed partner rank reconstructs the literal actual arc pairing;
no partner order or corner-packet property is assumed. -/
theorem paperAxisProperArcPartnerBoundaryRank_spec
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (t : paperAxisProperEndpointTag g hg a) :
    paperAxisProperEndpointBoundarySortedTag g hg a ha
      (paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t))
      (paperAxisProperArcPartnerBoundaryRank g hg a ha hproject t) =
        paperAxisProperArcEndpointPair g hg a t :=
  paperAxisProperEndpointBoundaryRank_spec g hg a ha hproject _

end Markov
