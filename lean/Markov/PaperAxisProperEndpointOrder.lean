import Markov.PaperAxisProperEndpointTags
import Markov.PaperQuadrilateralMarkedSideCoordinates

/-! Actual finite side sets and actual increasing marked-coordinate sorting
of genuine tagged endpoints. No endpoint-order witness is an input. -/
noncomputable section
open Set
namespace Markov

/-- The actual endpoint's free coordinate on its constructed actual side. -/
def paperAxisProperEndpointCoordinate (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a) : ℝ :=
  paperQuadrilateralMarkedSideCoordinate (paperAxisProperEndpointSide g hg a ha t)
    (paperAxisProperEndpointPoint g hg a ha t)

/-- Actual finite tags on the specified literal original side. -/
def paperAxisProperEndpointSideTags (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) :
    Finset (paperAxisProperEndpointTag g hg a) := by
  classical
  exact Finset.univ.filter (fun t => paperAxisProperEndpointSide g hg a ha t = k)

/-- Actual free-coordinate values of actual endpoint tags on that side. -/
def paperAxisProperEndpointSideCoordinates (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) : Finset ℝ := by
  classical
  exact (paperAxisProperEndpointSideTags g hg a ha k).image
    (paperAxisProperEndpointCoordinate g hg a ha)

/-- The actual coordinate of every tagged endpoint lies between deleted corners. -/
theorem paperAxisProperEndpointCoordinate_bounds (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a) :
    -1 < paperAxisProperEndpointCoordinate g hg a ha t ∧
      paperAxisProperEndpointCoordinate g hg a ha t < 1 :=
  paperQuadrilateralMarkedSideCoordinate_bounds _ _ (paperAxisProperEndpointSide_spec g hg a ha t)

/-- Genuine geometric point injection and the actual side-chart injection
prove coordinate injection on each actual finite side tag set. -/
theorem paperAxisProperEndpointCoordinate_injOn_side
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) (k : Fin 4) :
    Set.InjOn (paperAxisProperEndpointCoordinate g hg a ha)
      (paperAxisProperEndpointSideTags g hg a ha k) := by
  classical
  intro s hs t ht he
  have hs' : paperAxisProperEndpointSide g hg a ha s = k :=
    (Finset.mem_filter.mp hs).2
  have ht' : paperAxisProperEndpointSide g hg a ha t = k :=
    (Finset.mem_filter.mp ht).2
  apply paperAxisProperEndpointPoint_injective g hg a ha hproject
  apply paperQuadrilateralMarkedSideCoordinate_injective k
  · simpa only [hs'] using paperAxisProperEndpointSide_spec g hg a ha s
  · simpa only [ht'] using paperAxisProperEndpointSide_spec g hg a ha t
  · simpa only [paperAxisProperEndpointCoordinate, hs', ht'] using he

/-- Thus the constructed coordinate set has exactly the number of actual tags
on that side; sorting loses no distinct geometric endpoint. -/
theorem paperAxisProperEndpointSideCoordinates_card
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) (k : Fin 4) :
    (paperAxisProperEndpointSideCoordinates g hg a ha k).card =
      (paperAxisProperEndpointSideTags g hg a ha k).card := by
  classical
  exact Finset.card_image_of_injOn (paperAxisProperEndpointCoordinate_injOn_side
    g hg a ha hproject k)

/-- Literal increasing enumeration of the actual finite real coordinate set. -/
def paperAxisProperEndpointSideOrder (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) :
    Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card ↪o ℝ :=
  (paperAxisProperEndpointSideCoordinates g hg a ha k).orderEmbOfFin rfl

private theorem sortedTag_exists (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card) :
    ∃ t ∈ paperAxisProperEndpointSideTags g hg a ha k,
      paperAxisProperEndpointCoordinate g hg a ha t = paperAxisProperEndpointSideOrder g hg a ha k i := by
  classical
  exact Finset.mem_image.mp ((paperAxisProperEndpointSideCoordinates g hg a ha k).orderEmbOfFin_mem rfl i)

/-- Actual tagged endpoints chosen over the actual increasing coordinate table. -/
def paperAxisProperEndpointSortedTag (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card) :
    paperAxisProperEndpointTag g hg a :=
  (sortedTag_exists g hg a ha k i).choose

/-- The actual sorted tag is on the requested side and has exactly its table coordinate. -/
theorem paperAxisProperEndpointSortedTag_spec (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4)
    (i : Fin (paperAxisProperEndpointSideCoordinates g hg a ha k).card) :
    paperAxisProperEndpointSortedTag g hg a ha k i ∈ paperAxisProperEndpointSideTags g hg a ha k ∧
      paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperEndpointSortedTag g hg a ha k i) =
        paperAxisProperEndpointSideOrder g hg a ha k i :=
  (sortedTag_exists g hg a ha k i).choose_spec

/-- The sorted actual endpoint coordinates are genuinely strictly increasing. -/
theorem paperAxisProperEndpointSortedTag_strictMono (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) :
    StrictMono (fun i => paperAxisProperEndpointCoordinate g hg a ha
      (paperAxisProperEndpointSortedTag g hg a ha k i)) := by
  intro i j hij
  dsimp only
  rw [(paperAxisProperEndpointSortedTag_spec g hg a ha k i).2,
    (paperAxisProperEndpointSortedTag_spec g hg a ha k j).2]
  exact (paperAxisProperEndpointSideOrder g hg a ha k).strictMono hij

/-- Every actual tagged endpoint on the side appears in the actual sorted
list; genuine geometric coordinate injection proves the reverse inclusion. -/
theorem paperAxisProperEndpointSortedTag_range
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) (k : Fin 4) :
    Set.range (paperAxisProperEndpointSortedTag g hg a ha k) =
      (paperAxisProperEndpointSideTags g hg a ha k : Set (paperAxisProperEndpointTag g hg a)) := by
  classical
  ext t
  constructor
  · rintro ⟨i, rfl⟩
    exact (paperAxisProperEndpointSortedTag_spec g hg a ha k i).1
  · intro ht
    have hc : paperAxisProperEndpointCoordinate g hg a ha t ∈
        paperAxisProperEndpointSideCoordinates g hg a ha k :=
      Finset.mem_image.mpr ⟨t, ht, rfl⟩
    have hr : paperAxisProperEndpointCoordinate g hg a ha t ∈
        Set.range (paperAxisProperEndpointSideOrder g hg a ha k) := by
      change _ ∈ Set.range ((paperAxisProperEndpointSideCoordinates g hg a ha k).orderEmbOfFin rfl)
      rw [Finset.range_orderEmbOfFin]
      exact hc
    obtain ⟨i, hi⟩ := hr
    refine ⟨i, ?_⟩
    apply paperAxisProperEndpointCoordinate_injOn_side g hg a ha hproject k
      (paperAxisProperEndpointSortedTag_spec g hg a ha k i).1 ht
    exact (paperAxisProperEndpointSortedTag_spec g hg a ha k i).2.trans hi

end Markov
