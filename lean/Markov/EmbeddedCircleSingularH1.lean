import Markov.SingularCircleWinding
import Markov.ModularEmbeddedCircles
import Markov.ModularTraceSingularH1

/-! Genuine nonzero singular-H1 classes of the actual embedded affine circles.
Their actual continuous circle retractions give integer-valued H1 homomorphisms
that evaluate to one. This does not identify the original A/B coordinates. -/

noncomputable section
open Topology
namespace Markov

/-- Actual connecting paths at an arbitrary point of the actual modular quotient. -/
def modularArbitraryBaseConnector (x y : ModularTraceQuotient) : Path x y :=
  (modularTraceSingularConnector (modularTraceSingularRepresentative x) y).cast
    (modularTraceSingularRepresentative_spec x).symm rfl

/-- Actual connecting paths in the actual punctured two-circle torus,
transported through the proved quotient homeomorphism. -/
def standardPuncturedTorusConnector (x y : StandardPuncturedTorus) : Path x y :=
  ((modularArbitraryBaseConnector
    (modularTraceQuotientPuncturedTorusHomeomorph.symm x)
    (modularTraceQuotientPuncturedTorusHomeomorph.symm y)).map
      modularTraceQuotientPuncturedTorusHomeomorph.continuous).cast
        (modularTraceQuotientPuncturedTorusHomeomorph.apply_symm_apply x).symm
        (modularTraceQuotientPuncturedTorusHomeomorph.apply_symm_apply y).symm

/-- The actual integer-valued singular-H1 detector for a standard affine circle. -/
def standardAffineCircleH1Winding (p q : ℤ × ℤ) (hpq : intDet p q = 1)
    (c : NormalizedCircle) (hc : c ≠ 0) :
    integralSingularH1 StandardPuncturedTorus →+ ℤ :=
  singularH1CircleWinding (standardPuncturedAffineCircle p q hpq c hc 0)
    (standardPuncturedTorusConnector (standardPuncturedAffineCircle p q hpq c hc 0))
    (standardPuncturedTorusCircleRetraction q)
    (continuous_standardPuncturedTorusCircleRetraction q)
    (standardPuncturedAffineCircle_leftInverse p q hpq c hc 0)

@[simp] theorem standardAffineCircleH1Winding_loop (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : NormalizedCircle) (hc : c ≠ 0) :
    standardAffineCircleH1Winding p q hpq c hc
      (singularLoopClass StandardPuncturedTorus
        (standardPuncturedAffineCircleLoop p q hpq c hc)) = 1 :=
  singularH1CircleWinding_retract_standardLoop
    (continuous_standardPuncturedAffineCircle p q hpq c hc)
    (continuous_standardPuncturedTorusCircleRetraction q)
    (standardPuncturedAffineCircle_leftInverse p q hpq c hc)
    (standardPuncturedTorusConnector (standardPuncturedAffineCircle p q hpq c hc 0))

/-- The actual standard affine-circle loop is nonzero in actual integral H1. -/
theorem standardAffineCircleLoop_singularH1_ne_zero (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : NormalizedCircle) (hc : c ≠ 0) :
    singularLoopClass StandardPuncturedTorus
      (standardPuncturedAffineCircleLoop p q hpq c hc) ≠ 0 := by
  intro hz
  have hw := standardAffineCircleH1Winding_loop p q hpq c hc
  rw [hz, map_zero] at hw
  exact zero_ne_one hw

/-- The actual integer-valued singular-H1 detector for a modular affine circle. -/
def modularAffineCircleH1Winding (p q : ℤ × ℤ) (hpq : intDet p q = 1)
    (c : NormalizedCircle) (hc : c ≠ 0) :
    integralSingularH1 ModularTraceQuotient →+ ℤ :=
  singularH1CircleWinding (modularAffineCircle p q hpq c hc 0)
    (modularArbitraryBaseConnector (modularAffineCircle p q hpq c hc 0))
    (modularAffineCircleRetraction q)
    (continuous_modularAffineCircleRetraction q)
    (modularAffineCircle_leftInverse p q hpq c hc 0)

@[simp] theorem modularAffineCircleH1Winding_loop (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : NormalizedCircle) (hc : c ≠ 0) :
    modularAffineCircleH1Winding p q hpq c hc
      (singularLoopClass ModularTraceQuotient (modularAffineCircleLoop p q hpq c hc)) = 1 :=
  singularH1CircleWinding_retract_standardLoop
    (continuous_modularAffineCircle p q hpq c hc)
    (continuous_modularAffineCircleRetraction q)
    (modularAffineCircle_leftInverse p q hpq c hc)
    (modularArbitraryBaseConnector (modularAffineCircle p q hpq c hc 0))

/-- The actual modular affine-circle loop is nonzero in actual integral H1. -/
theorem modularAffineCircleLoop_singularH1_ne_zero (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : NormalizedCircle) (hc : c ≠ 0) :
    singularLoopClass ModularTraceQuotient (modularAffineCircleLoop p q hpq c hc) ≠ 0 := by
  intro hz
  have hw := modularAffineCircleH1Winding_loop p q hpq c hc
  rw [hz, map_zero] at hw
  exact zero_ne_one hw

/-- Every primitive standard-model direction has a genuine closed embedded
circle on the actual quotient whose actual singular H1 class is nonzero. -/
theorem modular_exists_embeddedAffineCircle_nonzero_singularH1 (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    ∃ q : ℤ × ℤ, ∃ hpq : intDet p q = 1,
      IsClosedEmbedding
        (modularAffineCircle p q hpq standardCircleHalf standardCircleHalf_ne_zero) ∧
      singularLoopClass ModularTraceQuotient
        (modularAffineCircleLoop p q hpq standardCircleHalf standardCircleHalf_ne_zero) ≠ 0 := by
  obtain ⟨q, hpq⟩ := standardPrimitive_complement p hp
  exact ⟨q, hpq, modularAffineCircle_isClosedEmbedding p q hpq
    standardCircleHalf standardCircleHalf_ne_zero,
    modularAffineCircleLoop_singularH1_ne_zero p q hpq
      standardCircleHalf standardCircleHalf_ne_zero⟩

end Markov
