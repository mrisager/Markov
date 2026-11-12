import Markov.PaperSimpleGeneratorCalibration
import Markov.PaperPrimitiveHolonomy

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- The actual restricted S-conjugation is involutive on the full nonabelian
subgroup. This uses its proved genuine free-basis action, not abelian coordinates. -/
theorem modularTraceSeedConjugation_involutive : Function.Involutive modularTraceSeedConjugation := by
  have h : modularTraceSeedConjugation.toMonoidHom.comp modularTraceSeedConjugation.toMonoidHom =
      MonoidHom.id modularTraceSubgroup := by
    apply paperTraceFreeGroupBasis.ext_hom
    intro i
    change modularTraceSeedConjugation (modularTraceSeedConjugation (paperTraceFreeGroupBasis i)) =
      paperTraceFreeGroupBasis i
    rw [modularTraceSeedConjugation_basis, map_inv, modularTraceSeedConjugation_basis, inv_inv]
  intro g
  exact DFunLike.congr_fun h g

/-- An actual upper-half-plane path from the calibrated original lift to the
initial point of the actual invariant axis. -/
def modularAxisCenterConnector (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    Path paperGeneratorCenterLift (modularHyperbolicAxis g hg 0) :=
  PathConnectedSpace.somePath _ _

/-- Its actual projected connector to the actual axis-period loop basepoint. -/
def modularAxisProjectedCenterConnector (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    Path paperGeneratorCenterPoint (modularClosedGeodesic g hg 0) :=
  (modularAxisCenterConnector g hg).map modularTraceQuotientMk_continuous

/-- The actual forward lifted axis-period loop transported to the original lift:
connector, axis segment, then the reversed deck-translated connector. Its
endpoint is literally g times the original lift. -/
def modularAxisCenterTransportLift (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    Path paperGeneratorCenterLift (g • paperGeneratorCenterLift) :=
  ((modularAxisCenterConnector g hg).trans (modularHyperbolicAxisSegment g hg)).trans
    ((modularAxisCenterConnector g hg).map (modularTraceSubgroup_isometry g).continuous).symm

/-- The actual projected forward axis-period loop at the calibrated original basepoint. -/
def modularAxisCenterTransportLoop (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    Path paperGeneratorCenterPoint paperGeneratorCenterPoint :=
  ((modularAxisCenterTransportLift g hg).map modularTraceQuotientMk_continuous).cast rfl
    (modularTraceQuotientMk_smul g paperGeneratorCenterLift).symm

/-- The projected transported lift is exactly the actual connector conjugate
of the actual forward closed-axis period loop, with the same traversal order. -/
theorem modularAxisCenterTransportLoop_eq_conjugate (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    modularAxisCenterTransportLoop g hg =
      ((modularAxisProjectedCenterConnector g hg).trans (modularClosedGeodesicLoop g hg)).trans
        (modularAxisProjectedCenterConnector g hg).symm := by
  ext t
  simp only [modularAxisCenterTransportLoop, modularAxisCenterTransportLift,
    modularAxisProjectedCenterConnector, Path.cast_coe, Path.map_coe,
    Function.comp_apply, Path.trans_apply, Path.symm_apply]
  split_ifs <;> first | rfl | exact modularTraceQuotientMk_smul g _

/-- The exact genuine original nonabelian marking is the whole-word
S-conjugation of the inverse forward endpoint, by the existing covering theorem. -/
theorem modularAxisCenterTransportLoop_marked (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk (modularAxisCenterTransportLoop g hg))) =
        modularTraceSeedConjugation g⁻¹ :=
  modularTraceMarkedFundamentalGroupEquiv_projectedPath paperGeneratorCenterLift g
    (modularAxisCenterTransportLift g hg)

/-- The actual projected upper-half-plane connector for the canonical paper holonomy. -/
def paperPrimitiveAxisProjectedConnector (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    Path paperGeneratorCenterPoint
      (modularClosedGeodesic (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp) 0) :=
  modularAxisProjectedCenterConnector (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp)

/-- The actual forward canonical axis-period loop, transported to the original basepoint. -/
def paperPrimitiveAxisTransportLoop (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    Path paperGeneratorCenterPoint paperGeneratorCenterPoint :=
  modularAxisCenterTransportLoop (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp)

/-- The canonical transported loop retains its actual connector and actual period-loop identity. -/
theorem paperPrimitiveAxisTransportLoop_eq_conjugate (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    paperPrimitiveAxisTransportLoop k p hp =
      ((paperPrimitiveAxisProjectedConnector k p hp).trans
        (modularClosedGeodesicLoop (paperPrimitiveHolonomy k p hp)
          (paperPrimitiveHolonomy_hyperbolic k p hp))).trans
        (paperPrimitiveAxisProjectedConnector k p hp).symm :=
  modularAxisCenterTransportLoop_eq_conjugate _ _

/-- Exact genuine marked class of the actual forward canonical axis loop:
raw canonical word inverse. Only the actual involution is used; general
S-conjugation is not replaced by inversion. No simplicity assertion is implicit. -/
theorem paperPrimitiveAxisTransportLoop_marked (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk (paperPrimitiveAxisTransportLoop k p hp))) =
        (quadrantPrimitiveTraceWord k p hp)⁻¹ := by
  change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
    (FundamentalGroup.fromPath (.mk
      (modularAxisCenterTransportLoop (paperPrimitiveHolonomy k p hp)
        (paperPrimitiveHolonomy_hyperbolic k p hp)))) = _
  rw [modularAxisCenterTransportLoop_marked, paperPrimitiveHolonomy, map_inv,
    modularTraceSeedConjugation_involutive]

end Markov
