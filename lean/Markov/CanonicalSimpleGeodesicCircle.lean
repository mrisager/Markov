import Markov.IntegerPeriodCircleDescent
import Markov.CanonicalAxisDeckSeparation
import Markov.ModularH1Transport

/-! Actual embedded metric geodesic circles for the constructed canonical
primitive data. The actual single-pair criterion has been proved separately by
finite disk crossing. The displayed forward once-around loop retains the genuine
fixed-I singular-H1 coordinates p. No arbitrary simple-class uniqueness or B_X
identification is asserted. -/

noncomputable section
open Set Topology
namespace Markov

private def periodCircleLoop (L : ℝ) : Path (0 : AddCircle L) 0 :=
  ((Path.segment (0 : ℝ) L).map (AddCircle.continuous_mk' L)).cast
    rfl (AddCircle.coe_period L).symm

private theorem periodCircleLoop_apply (L : ℝ) (t : unitInterval) :
    periodCircleLoop L t = (((t : ℝ)*L : ℝ) : AddCircle L) := by
  simp [periodCircleLoop, Path.segment_apply, AffineMap.lineMap_apply_module]

/-- The actual canonical axis descends to a literal continuous circle map at
its actual hyperbolic metric period. -/
def paperPrimitiveSimpleGeodesicCircle (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    C(AddCircle (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp)), ModularTraceQuotient) :=
  integerPeriodCircleMap (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp))
    (paperPrimitiveClosedGeodesic k p hp)
    (modularClosedGeodesic_continuous (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp))
    (paperPrimitiveClosedGeodesic_eq_iff_int_period k p hp)

/-- Every real representative retains the exact actual closed-geodesic value. -/
@[simp] theorem paperPrimitiveSimpleGeodesicCircle_coe (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) (t : ℝ) :
    paperPrimitiveSimpleGeodesicCircle k p hp
      (t : AddCircle (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp))) =
        paperPrimitiveClosedGeodesic k p hp t := rfl

/-- This is a genuine closed embedding of the actual period circle into the
actual quotient. No further geometric premise remains. -/
theorem paperPrimitiveSimpleGeodesicCircle_isClosedEmbedding (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    IsClosedEmbedding (paperPrimitiveSimpleGeodesicCircle k p hp) :=
  integerPeriodCircleMap_isClosedEmbedding _
    (modularClosedGeodesicPeriod_pos (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp))
    _ _ (paperPrimitiveClosedGeodesic_eq_iff_int_period k p hp)

/-- Its actual range is precisely the original canonical closed-geodesic range. -/
theorem paperPrimitiveSimpleGeodesicCircle_range (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    range (paperPrimitiveSimpleGeodesicCircle k p hp) = range (paperPrimitiveClosedGeodesic k p hp) :=
  integerPeriodCircleMap_range _ _ _ _

/-- Along real representatives the embedded circle has the checked local
unit-speed metric property of the actual projected hyperbolic axis. -/
theorem paperPrimitiveSimpleGeodesicCircle_local_dist_eq (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) (t : ℝ) :
    ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (paperPrimitiveSimpleGeodesicCircle k p hp
        (s : AddCircle (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp))))
        (paperPrimitiveSimpleGeodesicCircle k p hp
          (u : AddCircle (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp)))) = dist s u := by
  simpa only [paperPrimitiveSimpleGeodesicCircle_coe] using
    modularClosedGeodesic_local_dist_eq (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp) t

/-- The actual metric variation length of one period of the embedded geodesic
is the checked original numerical primitive trace length. -/
theorem paperPrimitiveSimpleGeodesicCircle_period_length (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    (eVariationOn (fun t : ℝ => paperPrimitiveSimpleGeodesicCircle k p hp
      (t : AddCircle (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp))))
        (Icc 0 (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp)))).toReal =
      primitiveSeedLength (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
        (quadrantCoordinates k p) hp := by
  simpa only [paperPrimitiveSimpleGeodesicCircle_coe] using
    (modularClosedGeodesic_period_length (paperPrimitiveHolonomy k p hp)
      (paperPrimitiveHolonomy_hyperbolic k p hp)).trans (paperPrimitiveHolonomy_period k p hp)

/-- The actual positive once-around loop of the actual embedded metric circle. -/
def paperPrimitiveSimpleGeodesicCircleLoop (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    Path (paperPrimitiveSimpleGeodesicCircle k p hp 0) (paperPrimitiveSimpleGeodesicCircle k p hp 0) :=
  (periodCircleLoop (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp))).map
    (paperPrimitiveSimpleGeodesicCircle k p hp).continuous

/-- The once-around embedded-circle loop is literally the already checked
actual forward period loop, including its actual basepoint and traversal. -/
theorem paperPrimitiveSimpleGeodesicCircleLoop_eq (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    paperPrimitiveSimpleGeodesicCircleLoop k p hp =
      modularClosedGeodesicLoop (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp) := by
  ext t
  change paperPrimitiveSimpleGeodesicCircle k p hp
    (periodCircleLoop (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp)) t) = _
  rw [periodCircleLoop_apply, paperPrimitiveSimpleGeodesicCircle_coe]
  rfl

/-- The actual embedded simple geodesic has precisely p in the single genuine
fixed-I singular-H1 marking, with the actual forward once-around orientation. -/
theorem paperPrimitiveSimpleGeodesicCircleLoop_fixedSingularCoordinates
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient (paperPrimitiveSimpleGeodesicCircleLoop k p hp)) = p := by
  rw [paperPrimitiveSimpleGeodesicCircleLoop_eq]
  exact paperPrimitiveClosedGeodesicLoop_fixedSingularCoordinates k p hp

end Markov
