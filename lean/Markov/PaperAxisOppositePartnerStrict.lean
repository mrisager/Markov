import Markov.PaperAxisOppositePartnerOrder
import Markov.PaperAxisBoundaryRanks

/-! Strict same-opposite partner order for the actual tagged boundary
coordinates. Equality is excluded using genuine same-side coordinate injection
and the actual ARC permutation, not an assumed strict matching field. -/

noncomputable section
open Set
namespace Markov

private theorem boundaryCoordinate_sign (j : Fin 4) (z : paperIdealQuadrilateral) :
    paperQuadrilateralBoundarySideCoordinate j z =
      if j=1 ∨ j=2 then -paperQuadrilateralMarkedSideCoordinate j z
      else paperQuadrilateralMarkedSideCoordinate j z := by
  fin_cases j <;> rfl

/-- The actual boundary-coordinate order of opposite-side ARC partners is
strictly reversed. All geometry is supplied by the checked weak obstruction;
actual side-coordinate and ARC injections exclude equality. -/
theorem paperAxisOppositePartner_boundary_strict
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (k : Fin 4) (t u : paperAxisProperEndpointTag g hg a)
    (ht0 : paperAxisProperEndpointSide g hg a ha t=k)
    (ht1 : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t)=
      paperQuadrilateralOppositeSide k)
    (hu0 : paperAxisProperEndpointSide g hg a ha u=k)
    (hu1 : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a u)=
      paperQuadrilateralOppositeSide k)
    (hx : paperAxisProperEndpointBoundaryCoordinate g hg a ha t<
      paperAxisProperEndpointBoundaryCoordinate g hg a ha u) :
    paperAxisProperEndpointBoundaryCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a u)<
      paperAxisProperEndpointBoundaryCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a t) := by
  classical
  have hx' : paperQuadrilateralBoundarySideCoordinate k (paperAxisProperEndpointPoint g hg a ha t)<
      paperQuadrilateralBoundarySideCoordinate k (paperAxisProperEndpointPoint g hg a ha u) := by
    simpa only [paperAxisProperEndpointBoundaryCoordinate,ht0,hu0] using hx
  have hle := paperAxisOppositePartner_boundary_antitone g hg a ha hproject k t u ht0 ht1 hu0 hu1 hx'
  have hle' : paperAxisProperEndpointBoundaryCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a u)≤
      paperAxisProperEndpointBoundaryCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a t) := by
    simpa only [paperAxisProperEndpointBoundaryCoordinate,hu1,ht1] using hle
  apply lt_of_le_of_ne hle'
  intro he
  have hm : paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a u)=
      paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a t) := by
    simp only [paperAxisProperEndpointBoundaryCoordinate,hu1,ht1,boundaryCoordinate_sign] at he
    simp only [paperAxisProperEndpointCoordinate,hu1,ht1]
    split_ifs at he with hj
    · exact neg_injective he
    · exact he
  have htags : paperAxisProperArcEndpointPair g hg a u=paperAxisProperArcEndpointPair g hg a t :=
    paperAxisProperEndpointCoordinate_injOn_side g hg a ha hproject (paperQuadrilateralOppositeSide k)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu1⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht1⟩) hm
  have hut : u=t := (paperAxisProperArcEndpointPair g hg a).injective htags
  subst u
  exact (lt_irrefl _) hx

end Markov
