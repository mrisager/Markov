import Markov.NormalizedCircleWinding
import Markov.StandardPrimitiveCircles

/-! Actual non-nullhomotopy of embedded affine circles in the punctured torus,
proved by mapping a hypothetical homotopy through the explicit circle retraction.
No original paper marking or singular-homology identification is asserted. -/

noncomputable section
open Topology
namespace Markov

/-- A continuous map with continuous left inverse reflects genuine path homotopy. -/
theorem pathHomotopic_of_continuous_leftInverse
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} {r : B → A} (hf : Continuous f) (hr : Continuous r)
    (hleft : Function.LeftInverse r f) {a b : A} {γ δ : Path a b}
    (h : (γ.map hf).Homotopic (δ.map hf)) : γ.Homotopic δ := by
  have h' := (h.map ⟨r, hr⟩).pathCast (hleft a).symm (hleft b).symm
  have hγ : (((γ.map hf).map hr).cast (hleft a).symm (hleft b).symm) = γ := by
    ext t
    exact hleft (γ t)
  have hδ : (((δ.map hf).map hr).cast (hleft a).symm (hleft b).symm) = δ := by
    ext t
    exact hleft (δ t)
  rwa [hγ, hδ] at h'

/-- The actual positive circle loop stays non-nullhomotopic under any
continuous map admitting a continuous circle retraction. -/
theorem normalizedCircleStandardLoop_map_not_homotopic_refl
    {X : Type*} [TopologicalSpace X]
    {f : NormalizedCircle → X} {r : X → NormalizedCircle}
    (hf : Continuous f) (hr : Continuous r) (hleft : Function.LeftInverse r f) :
    ¬ (normalizedCircleStandardLoop.map hf).Homotopic (Path.refl (f 0)) := by
  intro h
  apply normalizedCircleStandardLoop_not_homotopic_refl
  apply pathHomotopic_of_continuous_leftInverse hf hr hleft
  exact h

/-- The concrete affine-circle parametrization yields this actual based loop. -/
def standardPuncturedAffineCircleLoop (p q : ℤ × ℤ) (hpq : intDet p q = 1)
    (c : NormalizedCircle) (hc : c ≠ 0) :
    Path (standardPuncturedAffineCircle p q hpq c hc 0)
      (standardPuncturedAffineCircle p q hpq c hc 0) :=
  normalizedCircleStandardLoop.map
    (continuous_standardPuncturedAffineCircle p q hpq c hc)

/-- Every constructed affine circle has a genuinely non-nullhomotopic loop. -/
theorem standardPuncturedAffineCircleLoop_not_homotopic_refl
    (p q : ℤ × ℤ) (hpq : intDet p q = 1)
    (c : NormalizedCircle) (hc : c ≠ 0) :
    ¬ (standardPuncturedAffineCircleLoop p q hpq c hc).Homotopic
      (Path.refl (standardPuncturedAffineCircle p q hpq c hc 0)) := by
  exact normalizedCircleStandardLoop_map_not_homotopic_refl
    (continuous_standardPuncturedAffineCircle p q hpq c hc)
    (continuous_standardPuncturedTorusCircleRetraction q)
    (standardPuncturedAffineCircle_leftInverse p q hpq c hc)

/-- Every signed primitive direction has an actual closed embedded circle
whose positive once-around parametrization is not nullhomotopic. -/
theorem standardPrimitive_exists_nontrivialEmbeddedAffineCircle (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    ∃ q : ℤ × ℤ, ∃ hpq : intDet p q = 1,
      IsClosedEmbedding
        (standardPuncturedAffineCircle p q hpq standardCircleHalf standardCircleHalf_ne_zero) ∧
      ¬ (standardPuncturedAffineCircleLoop p q hpq standardCircleHalf
        standardCircleHalf_ne_zero).Homotopic
          (Path.refl (standardPuncturedAffineCircle p q hpq standardCircleHalf
            standardCircleHalf_ne_zero 0)) := by
  obtain ⟨q, hpq⟩ := standardPrimitive_complement p hp
  exact ⟨q, hpq,
    standardPuncturedAffineCircle_isClosedEmbedding p q hpq
      standardCircleHalf standardCircleHalf_ne_zero,
    standardPuncturedAffineCircleLoop_not_homotopic_refl p q hpq
      standardCircleHalf standardCircleHalf_ne_zero⟩

end Markov
