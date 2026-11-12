import Markov.PaperAxisProperEndpointOrder
import Markov.PaperAxisOppositeEndpointCounts
import Markov.PaperAxisProperDiagramConnected
import Mathlib.Data.Finset.Max

/-! Side-coordinate extrema in the endpoint diagram are preserved
by the edge pairing. The whole-diagram consequence takes closure under the
arc pairing as a hypothesis. `PaperAxisExtremeArcClosure` supplies this
closure when all four corner types occur. -/

noncomputable section
open Set
namespace Markov

/-- The actual tags minimal or maximal on their own actual original side. -/
def paperAxisExtremeEndpointSet
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) :
    Set (paperAxisProperEndpointTag g hg a) :=
  {t | (∀ u, paperAxisProperEndpointSide g hg a ha u =
        paperAxisProperEndpointSide g hg a ha t →
        paperAxisProperEndpointCoordinate g hg a ha t ≤
          paperAxisProperEndpointCoordinate g hg a ha u) ∨
      (∀ u, paperAxisProperEndpointSide g hg a ha u =
        paperAxisProperEndpointSide g hg a ha t →
        paperAxisProperEndpointCoordinate g hg a ha u ≤
          paperAxisProperEndpointCoordinate g hg a ha t)}

/-- An actual side has an actual least-coordinate tag, so the extrema set
is nonempty. Nonemptiness of the actual finite tag type is derived from the
proved lower bound on actual period cuts. -/
theorem paperAxisExtremeEndpointSet_nonempty
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) :
    (paperAxisExtremeEndpointSet g hg a ha).Nonempty := by
  classical
  have hc := paperAxisPeriodCutPoints_three_le_of_off_sides g hg a ha
  let t₀ : paperAxisProperEndpointTag g hg a := (⟨0, by omega⟩, 0)
  let T := paperAxisProperEndpointSideTags g hg a ha
    (paperAxisProperEndpointSide g hg a ha t₀)
  have ht₀ : t₀ ∈ T := by
    simp only [T, paperAxisProperEndpointSideTags, Finset.mem_filter,
      Finset.mem_univ, true_and]
  obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image T
    (paperAxisProperEndpointCoordinate g hg a ha) ⟨t₀, ht₀⟩
  have hside : paperAxisProperEndpointSide g hg a ha t =
      paperAxisProperEndpointSide g hg a ha t₀ := by
    simpa only [T, paperAxisProperEndpointSideTags, Finset.mem_filter,
      Finset.mem_univ, true_and] using ht
  refine ⟨t, Or.inl ?_⟩
  intro u hu
  apply hmin u
  simp only [T, paperAxisProperEndpointSideTags, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact hu.trans hside

/-- The actual quotient-edge pairing takes a side-coordinate extremum to
an extremum on the actual opposite side, using its proved side and coordinate
formulas. No arc-closure premise is used. -/
theorem paperAxisExtremeEndpointSet_edge_closed
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (t : paperAxisProperEndpointTag g hg a)
    (ht : t ∈ paperAxisExtremeEndpointSet g hg a ha) :
    paperAxisProperEdgePair g hg a t ∈ paperAxisExtremeEndpointSet g hg a ha := by
  have hedge (u : paperAxisProperEndpointTag g hg a) :=
    paperAxisProperEdgePair_opposite_and_coordinate g hg a ha hproject u
  have hcoord (u : paperAxisProperEndpointTag g hg a) :
      paperAxisProperEndpointCoordinate g hg a ha u =
        paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperEdgePair g hg a u) :=
    (hedge u).2
  have hside (u : paperAxisProperEndpointTag g hg a)
      (hu : paperAxisProperEndpointSide g hg a ha u =
        paperAxisProperEndpointSide g hg a ha (paperAxisProperEdgePair g hg a t)) :
      paperAxisProperEndpointSide g hg a ha (paperAxisProperEdgePair g hg a u) =
        paperAxisProperEndpointSide g hg a ha t := by
    rw [(hedge u).1, hu, (hedge t).1, paperQuadrilateralOppositeSide_apply_apply]
  rcases ht with hmin | hmax
  · refine Or.inl ?_
    intro u hu
    have hle := hmin (paperAxisProperEdgePair g hg a u) (hside u hu)
    simpa only [← hcoord t, ← hcoord u] using hle
  · refine Or.inr ?_
    intro u hu
    have hle := hmax (paperAxisProperEdgePair g hg a u) (hside u hu)
    simpa only [← hcoord t, ← hcoord u] using hle

/-- If actual arc closure is independently proved, actual connectedness and
the proved edge closure force the actual extrema set to be the whole diagram.
This theorem does not assert that the required arc closure holds. -/
theorem paperAxisExtremeEndpointSet_eq_univ_of_arc_closed
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (hArc : ∀ t ∈ paperAxisExtremeEndpointSet g hg a ha,
      paperAxisProperArcEndpointPair g hg a t ∈ paperAxisExtremeEndpointSet g hg a ha) :
    paperAxisExtremeEndpointSet g hg a ha = Set.univ :=
  paperAxisProperEndpoint_pair_closed_subset_eq_univ g hg a _
    (paperAxisExtremeEndpointSet_nonempty g hg a ha) hArc
    (paperAxisExtremeEndpointSet_edge_closed g hg a ha hproject)

end Markov
