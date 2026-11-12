import Markov.SeededWordCoordinates
import Markov.ModularMarkedLoops
import Markov.ModularClosedGeodesic

/-! Canonical primitive matrix words in the original paper marking, and
their actual closed metric geodesics. Coordinates below are the proved
algebraic abelianization coordinates. Singular H1, simplicity and unique
simple-geodesic representatives are not asserted or assumed. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- Actual S-conjugation restores the original paper marking. This is
conjugation of the entire matrix word, not inversion of its letters' order. -/
def paperPrimitiveHolonomy (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) : modularTraceSubgroup :=
  modularTraceSeedConjugation (quadrantPrimitiveTraceWord k p hp)

theorem paperPrimitiveHolonomy_coordinates (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    paperTraceAbelianizationCoordinates (paperPrimitiveHolonomy k p hp) =
      Multiplicative.ofAdd p := by
  rw [paperPrimitiveHolonomy, paperTraceAbelianizationCoordinates_seedConjugation,
    quadrantPrimitiveTraceWord_coordinates]
  change Multiplicative.ofAdd (-(-p)) = Multiplicative.ofAdd p
  rw [neg_neg]

theorem paperPrimitiveHolonomy_trace (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    ((paperPrimitiveHolonomy k p hp).val : IntMatrixTwo).trace =
      primitiveSeedTrace (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
        (quadrantCoordinates k p) hp := by
  change (paperSeedConjugation (quadrantPrimitiveTraceWord k p hp).val : IntMatrixTwo).trace = _
  rw [paperSeedConjugation_trace]
  rfl

theorem paperPrimitiveHolonomy_hyperbolic (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    2 < |((paperPrimitiveHolonomy k p hp).val : IntMatrixTwo).trace| := by
  rw [paperPrimitiveHolonomy_trace]
  have h := primitiveSeedTrace_ge_three _ _ (quadrantSeed_positiveFrickePair k)
    (quadrantCoordinates k p) hp
  have ha := le_abs_self (primitiveSeedTrace (quadrantSeedMatrices k).1
    (quadrantSeedMatrices k).2 (quadrantCoordinates k p) hp)
  omega

/-- The actual displayed metric period equals the existing numerical
primitive length, with its original trace normalization. -/
theorem paperPrimitiveHolonomy_period (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp) =
      primitiveSeedLength (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
        (quadrantCoordinates k p) hp := by
  rw [modularClosedGeodesicPeriod_trace _ (paperPrimitiveHolonomy_hyperbolic k p hp),
    paperPrimitiveHolonomy_trace]
  have h : (0 : ℝ) ≤ primitiveSeedTrace (quadrantSeedMatrices k).1
      (quadrantSeedMatrices k).2 (quadrantCoordinates k p) hp := by
    have hh := primitiveSeedTrace_ge_three _ _ (quadrantSeed_positiveFrickePair k)
      (quadrantCoordinates k p) hp
    exact_mod_cast (by omega : 0 ≤ primitiveSeedTrace (quadrantSeedMatrices k).1
      (quadrantSeedMatrices k).2 (quadrantCoordinates k p) hp)
  rw [abs_of_nonneg h]
  rfl

def paperPrimitiveClosedGeodesic (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) : ℝ → ModularTraceQuotient :=
  modularClosedGeodesic (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp)

theorem paperPrimitiveClosedGeodesic_periodic (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    Function.Periodic (paperPrimitiveClosedGeodesic k p hp)
      (primitiveSeedLength (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
        (quadrantCoordinates k p) hp) := by
  rw [← paperPrimitiveHolonomy_period]
  exact modularClosedGeodesic_periodic _ _

theorem paperPrimitiveClosedGeodesic_period_length (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    (eVariationOn (paperPrimitiveClosedGeodesic k p hp)
      (Set.Icc 0 (primitiveSeedLength (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
        (quadrantCoordinates k p) hp))).toReal =
      primitiveSeedLength (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
        (quadrantCoordinates k p) hp := by
  rw [← paperPrimitiveHolonomy_period]
  exact modularClosedGeodesic_period_length _ _

/-- Every actual projected path to a forward deck endpoint has the stated
marked algebraic coordinates, independently of the chosen path upstairs. -/
theorem modularTraceMarkedCoordinates_projectedPath (z : UpperHalfPlane)
    (g : modularTraceSubgroup) (γ : Path z (g • z)) :
    modularTraceMarkedCoordinates z (.fromPath (.mk
      ((γ.map modularTraceQuotientMk_continuous).cast rfl
        (modularTraceQuotientMk_smul g z).symm))) =
      paperTraceAbelianizationCoordinates g := by
  let δ := (γ.map modularTraceQuotientMk_continuous).cast rfl
    (modularTraceQuotientMk_smul g z).symm
  have he := coveringLoopEndpoint_projectedPath modularTraceQuotientMk_isCoveringMap
    γ (modularTraceQuotientMk_smul g z)
  have hd : modularTraceLoopDeckEquiv z (.mk δ) = g := by
    apply (modularTraceFibreEquiv z).injective
    rw [modularTraceLoopDeckEquiv_fibre]
    exact he
  change paperTraceAbelianizationCoordinates
    (modularTraceSeedConjugation ((modularTraceLoopDeckEquiv z (.mk δ))⁻¹)) = _
  rw [hd, paperTraceAbelianizationCoordinates_seedConjugation, map_inv, inv_inv]

/-- The closed axis loop has the specified positive primitive
coordinates in the algebraic abelianization of the marked group. -/
theorem paperPrimitiveClosedGeodesicLoop_coordinates (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    modularTraceMarkedCoordinates
      (modularHyperbolicAxis (paperPrimitiveHolonomy k p hp)
        (paperPrimitiveHolonomy_hyperbolic k p hp) 0)
      (.fromPath (.mk (modularClosedGeodesicLoop (paperPrimitiveHolonomy k p hp)
        (paperPrimitiveHolonomy_hyperbolic k p hp)))) = Multiplicative.ofAdd p := by
  simpa only [modularClosedGeodesicLoop] using
    (modularTraceMarkedCoordinates_projectedPath _ (paperPrimitiveHolonomy k p hp)
      (modularHyperbolicAxisSegment (paperPrimitiveHolonomy k p hp)
        (paperPrimitiveHolonomy_hyperbolic k p hp))).trans
      (paperPrimitiveHolonomy_coordinates k p hp)

end Markov
