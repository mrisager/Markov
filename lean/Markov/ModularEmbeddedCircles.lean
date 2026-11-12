import Markov.StandardPrimitiveCircles
import Markov.StandardPrimitiveCircleNontrivial
import Markov.PaperActualPuncturedTorus

noncomputable section
open Topology
namespace Markov

/-- The explicit puncture-avoiding affine circle in the actual modular quotient.
The integer label here refers to standard-model coordinates; no original A/B
homology or canonical-word identification is asserted by this definition. -/
def modularAffineCircle (p q : ℤ × ℤ) (hpq : intDet p q = 1)
    (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) :
    AddCircle (1 : ℝ) → ModularTraceQuotient :=
  modularTraceQuotientPuncturedTorusHomeomorph.symm ∘
    standardPuncturedAffineCircle p q hpq c hc

theorem continuous_modularAffineCircle (p q : ℤ × ℤ) (hpq : intDet p q = 1)
    (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) :
    Continuous (modularAffineCircle p q hpq c hc) :=
  modularTraceQuotientPuncturedTorusHomeomorph.symm.continuous.comp
    (continuous_standardPuncturedAffineCircle p q hpq c hc)

/-- These are genuine closed embedded circles on the actual quotient surface. -/
theorem modularAffineCircle_isClosedEmbedding (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) :
    IsClosedEmbedding (modularAffineCircle p q hpq c hc) :=
  modularTraceQuotientPuncturedTorusHomeomorph.symm.isClosedEmbedding.comp
    (standardPuncturedAffineCircle_isClosedEmbedding p q hpq c hc)

/-- The actual surface has a continuous circle retraction for each such choice. -/
def modularAffineCircleRetraction (q : ℤ × ℤ) :
    ModularTraceQuotient → AddCircle (1 : ℝ) :=
  standardPuncturedTorusCircleRetraction q ∘
    modularTraceQuotientPuncturedTorusHomeomorph

theorem continuous_modularAffineCircleRetraction (q : ℤ × ℤ) :
    Continuous (modularAffineCircleRetraction q) :=
  (continuous_standardPuncturedTorusCircleRetraction q).comp
    modularTraceQuotientPuncturedTorusHomeomorph.continuous

/-- The continuous dual coordinate is a left inverse on the actual surface. -/
theorem modularAffineCircle_leftInverse (p q : ℤ × ℤ) (hpq : intDet p q = 1)
    (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) :
    Function.LeftInverse (modularAffineCircleRetraction q)
      (modularAffineCircle p q hpq c hc) := by
  intro t
  change standardPuncturedTorusCircleRetraction q
    (modularTraceQuotientPuncturedTorusHomeomorph
      (modularTraceQuotientPuncturedTorusHomeomorph.symm
        (standardPuncturedAffineCircle p q hpq c hc t))) = t
  rw [Homeomorph.apply_symm_apply]
  exact standardPuncturedAffineCircle_leftInverse p q hpq c hc t

/-- Each primitive direction in the standard model gives an embedded
circle with a continuous left inverse on the modular surface. -/
theorem modular_exists_embeddedAffineCircle (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    ∃ q : ℤ × ℤ, ∃ hpq : intDet p q = 1,
      IsClosedEmbedding
        (modularAffineCircle p q hpq standardCircleHalf standardCircleHalf_ne_zero) ∧
      Function.LeftInverse (modularAffineCircleRetraction q)
        (modularAffineCircle p q hpq standardCircleHalf standardCircleHalf_ne_zero) := by
  obtain ⟨q, hpq⟩ := standardPrimitive_complement p hp
  exact ⟨q, hpq, modularAffineCircle_isClosedEmbedding p q hpq
    standardCircleHalf standardCircleHalf_ne_zero,
    modularAffineCircle_leftInverse p q hpq standardCircleHalf standardCircleHalf_ne_zero⟩

/-- The actual once-around loop on the embedded circle of the modular surface. -/
def modularAffineCircleLoop (p q : ℤ × ℤ) (hpq : intDet p q = 1)
    (c : NormalizedCircle) (hc : c ≠ 0) :
    Path (modularAffineCircle p q hpq c hc 0)
      (modularAffineCircle p q hpq c hc 0) :=
  normalizedCircleStandardLoop.map (continuous_modularAffineCircle p q hpq c hc)

/-- The loop on the actual quotient surface is genuinely non-nullhomotopic. -/
theorem modularAffineCircleLoop_not_homotopic_refl (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : NormalizedCircle) (hc : c ≠ 0) :
    ¬ (modularAffineCircleLoop p q hpq c hc).Homotopic
      (Path.refl (modularAffineCircle p q hpq c hc 0)) :=
  normalizedCircleStandardLoop_map_not_homotopic_refl
    (continuous_modularAffineCircle p q hpq c hc)
    (continuous_modularAffineCircleRetraction q)
    (modularAffineCircle_leftInverse p q hpq c hc)

/-- Each primitive direction of the standard model gives an embedded
non-nullhomotopic circle on the modular surface. -/
theorem modular_exists_nontrivialEmbeddedAffineCircle (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    ∃ q : ℤ × ℤ, ∃ hpq : intDet p q = 1,
      IsClosedEmbedding
        (modularAffineCircle p q hpq standardCircleHalf standardCircleHalf_ne_zero) ∧
      ¬ (modularAffineCircleLoop p q hpq standardCircleHalf
        standardCircleHalf_ne_zero).Homotopic
          (Path.refl (modularAffineCircle p q hpq standardCircleHalf
            standardCircleHalf_ne_zero 0)) := by
  obtain ⟨q, hpq⟩ := standardPrimitive_complement p hp
  exact ⟨q, hpq, modularAffineCircle_isClosedEmbedding p q hpq
    standardCircleHalf standardCircleHalf_ne_zero,
    modularAffineCircleLoop_not_homotopic_refl p q hpq
      standardCircleHalf standardCircleHalf_ne_zero⟩

end Markov
