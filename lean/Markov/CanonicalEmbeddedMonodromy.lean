import Markov.EmbeddedCircleRealLift
import Markov.CanonicalAxisMarkedClass
import Markov.ReversedEmbeddedCircles

noncomputable section
open Topology
namespace Markov

/-- The endpoint of the actual lift of the given connector from the original center. -/
def embeddedCircleConnectorLiftPoint
    (q : NormalizedCircle → ModularTraceQuotient)
    (d : Path paperGeneratorCenterPoint (q 0)) : UpperHalfPlane :=
  modularTraceQuotientMk_isCoveringMap.liftPath d paperGeneratorCenterLift d.source 1

/-- The actual lifted connector, with its endpoint retained. -/
def embeddedCircleConnectorLift
    (q : NormalizedCircle → ModularTraceQuotient)
    (d : Path paperGeneratorCenterPoint (q 0)) :
    Path paperGeneratorCenterLift (embeddedCircleConnectorLiftPoint q d) where
  toFun := modularTraceQuotientMk_isCoveringMap.liftPath d paperGeneratorCenterLift d.source
  continuous_toFun := ContinuousMap.continuous _
  source' := modularTraceQuotientMk_isCoveringMap.liftPath_zero d paperGeneratorCenterLift d.source
  target' := rfl

theorem embeddedCircleConnectorLiftPoint_project
    (q : NormalizedCircle → ModularTraceQuotient)
    (d : Path paperGeneratorCenterPoint (q 0)) :
    modularTraceQuotientMk (embeddedCircleConnectorLiftPoint q d) = q 0 := by
  have h := congr_fun (modularTraceQuotientMk_isCoveringMap.liftPath_lifts
    d paperGeneratorCenterLift d.source) 1
  exact h.trans d.target

theorem embeddedCircleConnectorLift_project
    (q : NormalizedCircle → ModularTraceQuotient)
    (d : Path paperGeneratorCenterPoint (q 0)) (t : unitInterval) :
    modularTraceQuotientMk (embeddedCircleConnectorLift q d t) = d t :=
  congr_fun (modularTraceQuotientMk_isCoveringMap.liftPath_lifts
    d paperGeneratorCenterLift d.source) t

/-- Positive circle monodromy at the actual connector endpoint. -/
def embeddedCircleConnectorDeck
    (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
    (d : Path paperGeneratorCenterPoint (q 0)) : modularTraceSubgroup :=
  embeddedCircleRealLiftDeck q hq (embeddedCircleConnectorLiftPoint q d)
    (embeddedCircleConnectorLiftPoint_project q d)

/-- The actual lifted transported once-around loop, ending at its literal forward deck translate. -/
def embeddedCircleConnectorTransportLift
    (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
    (d : Path paperGeneratorCenterPoint (q 0)) :
    Path paperGeneratorCenterLift (embeddedCircleConnectorDeck q hq d • paperGeneratorCenterLift) :=
  ((embeddedCircleConnectorLift q d).trans
    (embeddedCircleRealLiftUnitPath q hq (embeddedCircleConnectorLiftPoint q d)
      (embeddedCircleConnectorLiftPoint_project q d))).trans
    ((embeddedCircleConnectorLift q d).map
      (modularTraceSubgroup_isometry (embeddedCircleConnectorDeck q hq d)).continuous).symm

/-- Its exact actual projected loop at the original marked center. -/
def embeddedCircleConnectorTransportLoop
    (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
    (d : Path paperGeneratorCenterPoint (q 0)) :
    Path paperGeneratorCenterPoint paperGeneratorCenterPoint :=
  ((embeddedCircleConnectorTransportLift q hq d).map modularTraceQuotientMk_continuous).cast
    rfl (modularTraceQuotientMk_smul (embeddedCircleConnectorDeck q hq d)
      paperGeneratorCenterLift).symm

theorem embeddedCircleConnectorTransportLoop_eq
    (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
    (d : Path paperGeneratorCenterPoint (q 0)) :
    embeddedCircleConnectorTransportLoop q hq d =
      ((d.trans (normalizedCircleStandardLoop.map hq.continuous)).trans d.symm) := by
  ext t
  simp only [embeddedCircleConnectorTransportLoop, embeddedCircleConnectorTransportLift,
    Path.cast_coe, Path.map_coe, Function.comp_apply, Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact embeddedCircleConnectorLift_project q d _
  · change modularTraceQuotientMk (embeddedCircleRealLift q hq _ _ _) = _
    rw [embeddedCircleRealLift_project, normalizedCircleStandardLoop_apply]
  · rw [modularTraceQuotientMk_smul]
    exact embeddedCircleConnectorLift_project q d _

theorem embeddedCircleConnectorDeck_marked
    (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
    (d : Path paperGeneratorCenterPoint (q 0)) :
    modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk
        ((d.trans (normalizedCircleStandardLoop.map hq.continuous)).trans d.symm))) =
      modularTraceSeedConjugation (embeddedCircleConnectorDeck q hq d)⁻¹ := by
  rw [← embeddedCircleConnectorTransportLoop_eq]
  exact modularTraceMarkedFundamentalGroupEquiv_projectedPath paperGeneratorCenterLift _
    (embeddedCircleConnectorTransportLift q hq d)

/-- The genuine canonical nonabelian class discharges the literal unit-deck label,
using the actual lifted connector, not H1 or a conjugacy assumption. -/
theorem embeddedCircleConnectorDeck_eq_paperPrimitiveHolonomy
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p))
    (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
    (d : Path paperGeneratorCenterPoint (q 0))
    (hclass : modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk
        ((d.trans (normalizedCircleStandardLoop.map hq.continuous)).trans d.symm))) =
          (quadrantPrimitiveTraceWord k p hp)⁻¹) :
    embeddedCircleConnectorDeck q hq d = paperPrimitiveHolonomy k p hp := by
  have h : modularTraceSeedConjugation (embeddedCircleConnectorDeck q hq d)⁻¹ =
      (quadrantPrimitiveTraceWord k p hp)⁻¹ :=
    (embeddedCircleConnectorDeck_marked q hq d).symm.trans hclass
  have hD : modularTraceSeedConjugation (embeddedCircleConnectorDeck q hq d) =
      quadrantPrimitiveTraceWord k p hp := by
    apply inv_injective
    simpa only [map_inv] using h
  calc
    embeddedCircleConnectorDeck q hq d =
      modularTraceSeedConjugation (modularTraceSeedConjugation (embeddedCircleConnectorDeck q hq d)) :=
        (modularTraceSeedConjugation_involutive _).symm
    _ = modularTraceSeedConjugation (quadrantPrimitiveTraceWord k p hp) := congrArg _ hD
    _ = paperPrimitiveHolonomy k p hp := rfl

/-- Every canonical class has an actual embedded-circle lift whose unit deck
is literally the canonical hyperbolic holonomy, with the connector retained. -/
theorem paperPrimitiveHolonomy_has_embeddedCircle_monodromy
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    ∃ (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
      (d : Path paperGeneratorCenterPoint (q 0)),
      embeddedCircleConnectorDeck q hq d = paperPrimitiveHolonomy k p hp := by
  obtain ⟨q, hq, d, hclass⟩ := quadrantPrimitiveTraceWord_inverse_has_embeddedRepresentative k p hp
  exact ⟨q, hq, d, embeddedCircleConnectorDeck_eq_paperPrimitiveHolonomy k p hp q hq d hclass⟩

end Markov
