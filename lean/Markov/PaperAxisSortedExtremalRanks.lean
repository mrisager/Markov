import Markov.PaperAxisProperEndpointOrder

/-! Actual first/last side ranks satisfy the corresponding extremal
inequalities on the genuine computed endpoint set. This does not define the
root-owned extrema SET or assume any ARC-closure or nearest-corner theorem. -/
noncomputable section
open Set
namespace Markov

private theorem cornerRank_side_mem
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4)
    (t : paperAxisProperEndpointTag g hg a) (ht : paperAxisProperEndpointSide g hg a ha t = k) :
    t ∈ paperAxisProperEndpointSideTags g hg a ha k := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩

/-- The actual rank-zero endpoint is minimal among all actual endpoints on its side. -/
theorem paperAxisProperEndpointSortedTag_first_le
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (hn : 0 < (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (t : paperAxisProperEndpointTag g hg a) (ht : paperAxisProperEndpointSide g hg a ha t = k) :
    paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperEndpointSortedTag g hg a ha k ⟨0,hn⟩) ≤
      paperAxisProperEndpointCoordinate g hg a ha t := by
  have hr : t ∈ Set.range (paperAxisProperEndpointSortedTag g hg a ha k) := by
    rw [paperAxisProperEndpointSortedTag_range g hg a ha hproject]
    exact cornerRank_side_mem g hg a ha k t ht
  obtain ⟨i,rfl⟩ := hr
  exact (paperAxisProperEndpointSortedTag_strictMono g hg a ha k).monotone (Nat.zero_le _)

/-- The actual final-rank endpoint is maximal among all actual endpoints on its side. -/
theorem paperAxisProperEndpointSortedTag_le_last
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (hn : 0 < (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (t : paperAxisProperEndpointTag g hg a) (ht : paperAxisProperEndpointSide g hg a ha t = k) :
    paperAxisProperEndpointCoordinate g hg a ha t ≤
      paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperEndpointSortedTag g hg a ha k
        ⟨(paperAxisProperEndpointSideCoordinates g hg a ha k).card-1, Nat.sub_lt hn (by decide)⟩) := by
  have hr : t ∈ Set.range (paperAxisProperEndpointSortedTag g hg a ha k) := by
    rw [paperAxisProperEndpointSortedTag_range g hg a ha hproject]
    exact cornerRank_side_mem g hg a ha k t ht
  obtain ⟨i,rfl⟩ := hr
  apply (paperAxisProperEndpointSortedTag_strictMono g hg a ha k).monotone
  change i.val ≤ (paperAxisProperEndpointSideCoordinates g hg a ha k).card-1
  have := i.isLt
  omega

/-- Any genuine minimal endpoint is exactly the actual computed first rank. -/
theorem paperAxisProperEndpoint_eq_first_of_minimal
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (hn : 0 < (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (t : paperAxisProperEndpointTag g hg a) (ht : paperAxisProperEndpointSide g hg a ha t = k)
    (hmin : ∀ u : paperAxisProperEndpointTag g hg a, paperAxisProperEndpointSide g hg a ha u = k →
      paperAxisProperEndpointCoordinate g hg a ha t ≤ paperAxisProperEndpointCoordinate g hg a ha u) :
    t = paperAxisProperEndpointSortedTag g hg a ha k ⟨0,hn⟩ := by
  classical
  have hs := (paperAxisProperEndpointSortedTag_spec g hg a ha k ⟨0,hn⟩).1
  apply paperAxisProperEndpointCoordinate_injOn_side g hg a ha hproject k
    (cornerRank_side_mem g hg a ha k t ht) hs
  apply le_antisymm (hmin _ (Finset.mem_filter.mp hs).2)
  exact paperAxisProperEndpointSortedTag_first_le g hg a ha hproject k hn t ht

/-- Any genuine maximal endpoint is exactly the actual computed final rank. -/
theorem paperAxisProperEndpoint_eq_last_of_maximal
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4)
    (hn : 0 < (paperAxisProperEndpointSideCoordinates g hg a ha k).card)
    (t : paperAxisProperEndpointTag g hg a) (ht : paperAxisProperEndpointSide g hg a ha t = k)
    (hmax : ∀ u : paperAxisProperEndpointTag g hg a, paperAxisProperEndpointSide g hg a ha u = k →
      paperAxisProperEndpointCoordinate g hg a ha u ≤ paperAxisProperEndpointCoordinate g hg a ha t) :
    t = paperAxisProperEndpointSortedTag g hg a ha k
      ⟨(paperAxisProperEndpointSideCoordinates g hg a ha k).card-1, Nat.sub_lt hn (by decide)⟩ := by
  classical
  have hs := (paperAxisProperEndpointSortedTag_spec g hg a ha k
    ⟨(paperAxisProperEndpointSideCoordinates g hg a ha k).card-1, Nat.sub_lt hn (by decide)⟩).1
  apply paperAxisProperEndpointCoordinate_injOn_side g hg a ha hproject k
    (cornerRank_side_mem g hg a ha k t ht) hs
  apply le_antisymm
  · exact paperAxisProperEndpointSortedTag_le_last g hg a ha hproject k hn t ht
  · exact hmax _ (Finset.mem_filter.mp hs).2

end Markov
