import Markov.CanonicalSimpleGeodesicCircle
import Markov.CanonicalTraceNormPeriods

noncomputable section
open Set Topology
namespace Markov

/-- Every original signed primitive lattice class has an actual canonical
closed embedded locally unit-speed geodesic circle. Its literal representative,
actual forward once-around loop and genuine fixed-I H1 label are retained, and
its actual one-period metric variation equals the constructed trace norm.
This is existence only, not classification of arbitrary simple classes. -/
theorem primitive_signedClass_has_canonical_simpleGeodesicCircle
    (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    ∃ k : Fin 4, ∃ hkp : NonnegativePrimitiveDirection (quadrantCoordinates k p),
      IsClosedEmbedding (paperPrimitiveSimpleGeodesicCircle k p hkp) ∧
      (∀ t : ℝ, paperPrimitiveSimpleGeodesicCircle k p hkp
        (t : AddCircle (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hkp))) =
          paperPrimitiveClosedGeodesic k p hkp t) ∧
      range (paperPrimitiveSimpleGeodesicCircle k p hkp) =
        range (paperPrimitiveClosedGeodesic k p hkp) ∧
      (∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
        dist (paperPrimitiveSimpleGeodesicCircle k p hkp
          (s : AddCircle (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hkp))))
          (paperPrimitiveSimpleGeodesicCircle k p hkp
            (u : AddCircle (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hkp)))) =
              dist s u) ∧
      paperPrimitiveSimpleGeodesicCircleLoop k p hkp =
        modularClosedGeodesicLoop (paperPrimitiveHolonomy k p hkp)
          (paperPrimitiveHolonomy_hyperbolic k p hkp) ∧
      modularTraceFixedSingularH1Equiv
        (singularLoopClass ModularTraceQuotient (paperPrimitiveSimpleGeodesicCircleLoop k p hkp)) = p ∧
      modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hkp) = ‖intVector traceBasis p‖ ∧
      (eVariationOn (fun t : ℝ => paperPrimitiveSimpleGeodesicCircle k p hkp
        (t : AddCircle (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hkp))))
          (Icc 0 (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hkp)))).toReal =
            ‖intVector traceBasis p‖ := by
  obtain ⟨k, hx, hy⟩ := exists_nonnegative_quadrantCoordinates p
  have hkp : NonnegativePrimitiveDirection (quadrantCoordinates k p) :=
    ⟨hx, hy, quadrantCoordinates_coprime k p hp⟩
  exact ⟨k, hkp, paperPrimitiveSimpleGeodesicCircle_isClosedEmbedding k p hkp,
    paperPrimitiveSimpleGeodesicCircle_coe k p hkp,
    paperPrimitiveSimpleGeodesicCircle_range k p hkp,
    paperPrimitiveSimpleGeodesicCircle_local_dist_eq k p hkp,
    paperPrimitiveSimpleGeodesicCircleLoop_eq k p hkp,
    paperPrimitiveSimpleGeodesicCircleLoop_fixedSingularCoordinates k p hkp,
    paperPrimitiveHolonomy_period_eq_trace_norm k p hkp,
    (paperPrimitiveSimpleGeodesicCircle_period_length k p hkp).trans
      (norm_intVector_quadrant k p hkp).symm⟩

end Markov
