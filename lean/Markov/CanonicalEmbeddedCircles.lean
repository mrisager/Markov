import Markov.OriginalGeometricEmbeddedCircles
import Markov.SeededGeometricRealization

noncomputable section
open Topology
namespace Markov

/-- Every genuinely realized original generator has a literal actual closed
embedded circle and connector whose positive once-around conjugate has exactly
the prescribed nonabelian marked value. -/
theorem OriginalGeometricGenerator.has_embeddedRepresentative
    {g : modularTraceSubgroup} (hg : OriginalGeometricGenerator g) :
    ∃ (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
      (d : Path paperGeneratorCenterPoint (q 0)),
      modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
        (FundamentalGroup.fromPath (.mk
          ((d.trans (normalizedCircleStandardLoop.map hq.continuous)).trans d.symm))) = g := by
  rcases hg with ⟨f, c, i, he⟩
  obtain ⟨q, hq, d, hclass⟩ := originalMarkedHomeomorph_generator_has_embeddedRepresentative f c i
  exact ⟨q, hq, d, hclass.trans he⟩

/-- Every literal RAW signed canonical primitive word has an actual closed
embedded circle representative with its exact original nonabelian marked class.
This is a raw-word statement; a forward paperPrimitiveHolonomy axis has marked
class raw-word inverse, and no geodesic simplicity is asserted here. -/
theorem quadrantPrimitiveTraceWord_has_embeddedRepresentative (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    ∃ (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
      (d : Path paperGeneratorCenterPoint (q 0)),
      modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
        (FundamentalGroup.fromPath (.mk
          ((d.trans (normalizedCircleStandardLoop.map hq.continuous)).trans d.symm))) =
          quadrantPrimitiveTraceWord k p hp :=
  (quadrantPrimitiveTraceWord_geometricGenerator k p hp).has_embeddedRepresentative

end Markov
