import Markov.PaperAxisProperEndpointTags
import Markov.PaperQuadrilateralOppositeGluing

/-! Actual target-to-next-source cyclic endpoint gluing lies on opposite
original sides and preserves the literal marked-square free coordinate.
Distinct Q-values are proved from the actual finite endpoint-tag injection. -/

noncomputable section
open Set
namespace Markov

/-- Each actual cyclic target-to-source gluing has opposite literal side
indices and exactly equal actual marked-square free coordinates. -/
theorem paperAxisProperEndpoint_cyclic_gluing_opposite_and_coordinate
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (i : paperAxisProperArcIndex g hg a) :
    paperAxisProperEndpointSide g hg a ha (paperAxisProperArcNextIndex g hg a i, 0) =
        paperQuadrilateralOppositeSide (paperAxisProperEndpointSide g hg a ha (i, 1)) ∧
      paperQuadrilateralMarkedSideCoordinate (paperAxisProperEndpointSide g hg a ha (i, 1))
          (paperAxisProperEndpointPoint g hg a ha (i, 1)) =
        paperQuadrilateralMarkedSideCoordinate
          (paperAxisProperEndpointSide g hg a ha (paperAxisProperArcNextIndex g hg a i, 0))
          (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcNextIndex g hg a i, 0)) := by
  have hne : paperAxisProperEndpointPoint g hg a ha (i, 1) ≠
      paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcNextIndex g hg a i, 0) := by
    intro heq
    have htags := paperAxisProperEndpointPoint_injective g hg a ha hproject heq
    have hend := congrArg (fun t : paperAxisProperEndpointTag g hg a => t.2) htags
    norm_num at hend
  exact paperQuadrilateral_distinct_projected_eq_opposite_and_coordinate _ _ hne
    (paperAxisProperArc_projected_gluing g hg a ha i) _ _
    (paperAxisProperEndpointSide_spec g hg a ha (i, 1))
    (paperAxisProperEndpointSide_spec g hg a ha (paperAxisProperArcNextIndex g hg a i, 0))

end Markov
