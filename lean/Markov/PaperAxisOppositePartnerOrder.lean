import Markov.RawSquareOppositePacketOrder

/-! Same-opposite-packet order for the actual proper family. Its full closed
arc separation follows from actual all-phase projected-period injectivity.
No partner-order, rank-offset, or class/norm field is supplied. -/

noncomputable section
open Set
namespace Markov

/-- In every actual opposite-side packet, increasing raw clockwise source
coordinates force nonincreasing raw clockwise ARC-partner coordinates. Actual
side geometry constructs the crossing contradiction and actual family separation
rules it out, including all endpoint parameters. -/
theorem paperAxisOppositePartner_raw_antitone
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
    (hx : paperQuadrilateralRawBoundarySideCoordinate k (paperAxisProperEndpointPoint g hg a ha t)<
      paperQuadrilateralRawBoundarySideCoordinate k (paperAxisProperEndpointPoint g hg a ha u)) :
    paperQuadrilateralRawBoundarySideCoordinate (paperQuadrilateralOppositeSide k)
        (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a u))≤
      paperQuadrilateralRawBoundarySideCoordinate (paperQuadrilateralOppositeSide k)
        (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t)) := by
  have hne : t≠u := by
    intro he
    subst u
    exact (lt_irrefl _) hx
  have hindices : t.1≠u.1 := paperAxisProperEndpoint_same_side_arcIndex_ne
    g hg a ha t u hne (ht0.trans hu0.symm)
  let q := (paperAxisArcFromTag g hg a ha t).toContinuousMap
  let r := (paperAxisArcFromTag g hg a ha u).toContinuousMap
  have hq0 : q 0=paperAxisProperEndpointPoint g hg a ha t := (paperAxisArcFromTag g hg a ha t).source
  have hq1 : q 1=paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t) :=
    (paperAxisArcFromTag g hg a ha t).target
  have hr0 : r 0=paperAxisProperEndpointPoint g hg a ha u := (paperAxisArcFromTag g hg a ha u).source
  have hr1 : r 1=paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a u) :=
    (paperAxisArcFromTag g hg a ha u).target
  have hq0side : (q 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide k := by
    rw [hq0]
    simpa only [ht0] using paperAxisProperEndpointSide_spec g hg a ha t
  have hq1side : (q 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide (paperQuadrilateralOppositeSide k) := by
    rw [hq1]
    simpa only [ht1] using paperAxisProperEndpointSide_spec g hg a ha (paperAxisProperArcEndpointPair g hg a t)
  have hr0side : (r 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide k := by
    rw [hr0]
    simpa only [hu0] using paperAxisProperEndpointSide_spec g hg a ha u
  have hr1side : (r 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide (paperQuadrilateralOppositeSide k) := by
    rw [hr1]
    simpa only [hu1] using paperAxisProperEndpointSide_spec g hg a ha (paperAxisProperArcEndpointPair g hg a u)
  have hx' : paperQuadrilateralRawBoundarySideCoordinate k (q 0)<
      paperQuadrilateralRawBoundarySideCoordinate k (r 0) := by
    simpa only [hq0,hr0] using hx
  have horder := paperQuadrilateral_opposite_raw_partner_antitone k q r hq0side hq1side hr0side hr1side
    (fun s hs0 hs1 => paperAxisArcFromTag_strict g hg a ha t s hs0 hs1)
    (fun s hs0 hs1 => paperAxisArcFromTag_strict g hg a ha u s hs0 hs1)
    (fun s v => paperAxisArcFromTag_points_ne g hg a ha hproject t u hindices s v) hx'
  simpa only [hq1,hr1] using horder

/-- The same actual partner order in the actual normalized marked clockwise
boundary coordinates used by the checked finite side sorting. -/
theorem paperAxisOppositePartner_boundary_antitone
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
    (hx : paperQuadrilateralBoundarySideCoordinate k (paperAxisProperEndpointPoint g hg a ha t)<
      paperQuadrilateralBoundarySideCoordinate k (paperAxisProperEndpointPoint g hg a ha u)) :
    paperQuadrilateralBoundarySideCoordinate (paperQuadrilateralOppositeSide k)
        (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a u))≤
      paperQuadrilateralBoundarySideCoordinate (paperQuadrilateralOppositeSide k)
        (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t)) := by
  have ht0side : (paperAxisProperEndpointPoint g hg a ha t).val∈paperQuadrilateralGeodesicSide k := by
    simpa only [ht0] using paperAxisProperEndpointSide_spec g hg a ha t
  have hu0side : (paperAxisProperEndpointPoint g hg a ha u).val∈paperQuadrilateralGeodesicSide k := by
    simpa only [hu0] using paperAxisProperEndpointSide_spec g hg a ha u
  have ht1side : (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t)).val∈
      paperQuadrilateralGeodesicSide (paperQuadrilateralOppositeSide k) := by
    simpa only [ht1] using paperAxisProperEndpointSide_spec g hg a ha (paperAxisProperArcEndpointPair g hg a t)
  have hu1side : (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a u)).val∈
      paperQuadrilateralGeodesicSide (paperQuadrilateralOppositeSide k) := by
    simpa only [hu1] using paperAxisProperEndpointSide_spec g hg a ha (paperAxisProperArcEndpointPair g hg a u)
  have hx' := (paperQuadrilateralBoundarySideCoordinate_raw_lt_iff k _ _ ht0side hu0side).mp hx
  have horder := paperAxisOppositePartner_raw_antitone g hg a ha hproject k t u ht0 ht1 hu0 hu1 hx'
  exact (paperQuadrilateralBoundarySideCoordinate_raw_le_iff (paperQuadrilateralOppositeSide k)
    _ _ hu1side ht1side).mpr horder

end Markov
