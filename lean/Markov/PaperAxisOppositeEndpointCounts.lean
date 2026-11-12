import Markov.PaperAxisProperEndpointPairings
import Markov.PaperQuadrilateralOppositeGluing

/-! Actual quotient-edge endpoint pairing exchanges opposite original sides
and preserves the literal marked-square free coordinate. Restricting this
constructed permutation gives an actual equivalence of opposite side fibers,
so their actual finite endpoint counts are equal. No count-balance field or
normal-diagram classifier is assumed. -/

noncomputable section
open Set
namespace Markov

/-- The constructed actual quotient-edge pairing exchanges opposite literal
side labels and preserves actual marked-square free coordinates. -/
theorem paperAxisProperEdgePair_opposite_and_coordinate
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (t : paperAxisProperEndpointTag g hg a) :
    paperAxisProperEndpointSide g hg a ha (paperAxisProperEdgePair g hg a t) =
        paperQuadrilateralOppositeSide (paperAxisProperEndpointSide g hg a ha t) ∧
      paperQuadrilateralMarkedSideCoordinate (paperAxisProperEndpointSide g hg a ha t)
          (paperAxisProperEndpointPoint g hg a ha t) =
        paperQuadrilateralMarkedSideCoordinate
          (paperAxisProperEndpointSide g hg a ha (paperAxisProperEdgePair g hg a t))
          (paperAxisProperEndpointPoint g hg a ha (paperAxisProperEdgePair g hg a t)) :=
  paperQuadrilateral_distinct_projected_eq_opposite_and_coordinate _ _
    (paperAxisProperEdgePair_points_ne g hg a ha hproject t)
    (paperAxisProperEdgePair_project g hg a ha t) _ _
    (paperAxisProperEndpointSide_spec g hg a ha t)
    (paperAxisProperEndpointSide_spec g hg a ha (paperAxisProperEdgePair g hg a t))

/-- Restriction of the actual edge permutation to the actual opposite-side
endpoint fibers. This constructs the bijection used for finite count balance. -/
def paperAxisProperOppositeEndpointEquiv
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4) :
    {t : paperAxisProperEndpointTag g hg a // paperAxisProperEndpointSide g hg a ha t = k} ≃
      {t : paperAxisProperEndpointTag g hg a //
        paperAxisProperEndpointSide g hg a ha t = paperQuadrilateralOppositeSide k} := by
  classical
  apply Equiv.subtypeEquiv (paperAxisProperEdgePair g hg a)
  intro t
  rw [(paperAxisProperEdgePair_opposite_and_coordinate g hg a ha hproject t).1]
  exact ⟨fun h => congrArg paperQuadrilateralOppositeSide h,
    fun h => paperQuadrilateralOppositeSide.injective h⟩

/-- The literal number of actual tagged endpoints on each original side. -/
def paperAxisProperEndpointSideCount
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) : ℕ := by
  classical
  exact Fintype.card {t : paperAxisProperEndpointTag g hg a //
    paperAxisProperEndpointSide g hg a ha t = k}

/-- Counts on opposite original sides are equal, proved from the actual
constructed edge permutation and the actual finite endpoint side fibers. -/
theorem paperAxisProperEndpointSideCount_eq_opposite
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) (k : Fin 4) :
    paperAxisProperEndpointSideCount g hg a ha k =
      paperAxisProperEndpointSideCount g hg a ha (paperQuadrilateralOppositeSide k) := by
  classical
  exact Fintype.card_congr (paperAxisProperOppositeEndpointEquiv g hg a ha hproject k)

end Markov
