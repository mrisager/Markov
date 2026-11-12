import Markov.ReversedEmbeddedCircles
import Markov.CanonicalAxisMarkedClass

/-! Exact genuine based homotopy from the transported forward canonical axis
period loop to an actual embedded circle representative. This identifies its
free class through the actual nonabelian marking; it does not assert that the
axis itself is simple, embedded, or the unique geodesic in that class. -/

noncomputable section
open Topology
namespace Markov

/-- The actual forward canonical axis period, transported by its actual
upper-half-plane connector to the common center, is genuinely path homotopic
to a positive once-around actual closed embedded circle with its own actual
connector. The inverse raw-word orientation is retained exactly. -/
theorem paperPrimitiveAxisTransportLoop_has_embeddedRepresentative
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    ∃ (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
      (d : Path paperGeneratorCenterPoint (q 0)),
      (paperPrimitiveAxisTransportLoop k p hp).Homotopic
        ((d.trans (normalizedCircleStandardLoop.map hq.continuous)).trans d.symm) := by
  obtain ⟨q, hq, d, hg⟩ := quadrantPrimitiveTraceWord_inverse_has_embeddedRepresentative k p hp
  refine ⟨q, hq, d, ?_⟩
  have he : FundamentalGroup.fromPath (.mk (paperPrimitiveAxisTransportLoop k p hp)) =
      FundamentalGroup.fromPath (.mk
        ((d.trans (normalizedCircleStandardLoop.map hq.continuous)).trans d.symm)) :=
    (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).injective
      ((paperPrimitiveAxisTransportLoop_marked k p hp).trans hg.symm)
  exact Path.Homotopic.Quotient.eq.mp he

end Markov
