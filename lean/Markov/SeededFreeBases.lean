import Markov.FreeBasisFareyMoves
import Markov.PaperPrimitiveHolonomy

/-! Genuine free generating pairs for the actual signed Farey matrix words.
The canonical words are proved literally to belong to free bases of the
actual subgroup. This is group primitiveness, not a simple-curve or singular
homology assertion. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- Two literal integral matrices are the ordered generators of an actual
free basis of the actual modular trace subgroup. -/
def TraceFreeBasisPair (M N : IntMatrixTwo) : Prop :=
  ∃ b : FreeGroupBasis (Fin 2) modularTraceSubgroup,
    ((b 0).val : IntMatrixTwo) = M ∧ ((b 1).val : IntMatrixTwo) = N

/-- Each signed quadrant starts with a genuine ordered free basis. -/
theorem quadrantSeed_freeBasisPair (k : Fin 4) :
    TraceFreeBasisPair (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 := by
  let b := paperTraceFreeGroupBasis
  have ha : (b 0 : SL(2, ℤ)) = paperGeneratorASL := paperTraceFreeGroupBasis_zero
  have hb : (b 1 : SL(2, ℤ)) = paperGeneratorBSL := paperTraceFreeGroupBasis_one
  fin_cases k
  · refine ⟨freeBasisInvertAt (freeBasisInvertAt b 0) 1, ?_, ?_⟩
    · simp only [freeBasisInvertAt_apply]
      change (((b 0 : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : IntMatrixTwo) = modularGeneratorA
      rw [ha, ← modularGeneratorASL_eq_paperGeneratorASL_inv]
      rfl
    · simp only [freeBasisInvertAt_apply]
      change (((b 1 : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : IntMatrixTwo) = modularGeneratorB
      rw [hb, ← modularGeneratorBSL_eq_paperGeneratorBSL_inv]
      rfl
  · refine ⟨freeBasisSwap (freeBasisInvertAt b 1), ?_, ?_⟩
    · simp only [freeBasisSwap_zero, freeBasisInvertAt_apply]
      change (((b 1 : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : IntMatrixTwo) = modularGeneratorB
      rw [hb, ← modularGeneratorBSL_eq_paperGeneratorBSL_inv]
      rfl
    · simp only [freeBasisSwap_one, freeBasisInvertAt_apply]
      change ((b 0).val : IntMatrixTwo) = modularGeneratorA.adjugate
      rw [ha]
      norm_num [paperGeneratorASL, paperGeneratorA, modularGeneratorA, Matrix.adjugate_fin_two]
  · refine ⟨b, ?_, ?_⟩
    · change ((b 0).val : IntMatrixTwo) = modularGeneratorA.adjugate
      rw [ha]
      norm_num [paperGeneratorASL, paperGeneratorA, modularGeneratorA, Matrix.adjugate_fin_two]
    · change ((b 1).val : IntMatrixTwo) = modularGeneratorB.adjugate
      rw [hb]
      norm_num [paperGeneratorBSL, paperGeneratorB, modularGeneratorB, Matrix.adjugate_fin_two]
  · refine ⟨freeBasisSwap (freeBasisInvertAt b 0), ?_, ?_⟩
    · simp only [freeBasisSwap_zero, freeBasisInvertAt_apply]
      change ((b 1).val : IntMatrixTwo) = modularGeneratorB.adjugate
      rw [hb]
      norm_num [paperGeneratorBSL, paperGeneratorB, modularGeneratorB, Matrix.adjugate_fin_two]
    · simp only [freeBasisSwap_one, freeBasisInvertAt_apply]
      change (((b 0 : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : IntMatrixTwo) = modularGeneratorA
      rw [ha, ← modularGeneratorASL_eq_paperGeneratorASL_inv]
      rfl

/-- The actual Farey matrix products preserve an actual ordered free basis;
labels play no role in this group-theoretic assertion. -/
theorem SeededFarey.freeBasisPair {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey u0 v0 M0 N0 u v M N) (h0 : TraceFreeBasisPair M0 N0) :
    TraceFreeBasisPair M N := by
  induction h with
  | seed => exact h0
  | left _ ih =>
    obtain ⟨b, hM, hN⟩ := ih
    refine ⟨freeBasisFareyLeft b, ?_, ?_⟩
    · simpa only [freeBasisFareyLeft_zero] using hM
    · rw [freeBasisFareyLeft_one]
      change ((b 0).val : IntMatrixTwo) * ((b 1).val : IntMatrixTwo) = _
      rw [hM, hN]
  | right _ ih =>
    obtain ⟨b, hM, hN⟩ := ih
    refine ⟨freeBasisFareyRight b, ?_, ?_⟩
    · rw [freeBasisFareyRight_zero]
      change ((b 0).val : IntMatrixTwo) * ((b 1).val : IntMatrixTwo) = _
      rw [hM, hN]
    · simpa only [freeBasisFareyRight_one] using hN

/-- Every actual signed-quadrant Farey pair freely generates the subgroup. -/
theorem SeededFarey.quadrant_freeBasisPair {k : Fin 4} {u v : ℤ × ℤ}
    {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N) :
    TraceFreeBasisPair M N :=
  h.freeBasisPair (quadrantSeed_freeBasisPair k)

/-- Genuine group primitiveness: an element is literally one generator of
an actual two-element free basis of the actual subgroup. -/
def TraceFreeBasisGenerator (g : modularTraceSubgroup) : Prop :=
  ∃ b : FreeGroupBasis (Fin 2) modularTraceSubgroup, ∃ i : Fin 2, b i = g

/-- The canonical signed primitive word is genuinely a free-basis generator,
not merely an element with primitive abelianization coordinates. -/
theorem quadrantPrimitiveTraceWord_freeBasisGenerator (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    TraceFreeBasisGenerator (quadrantPrimitiveTraceWord k p hp) := by
  rcases primitiveSeedMatrix_spec (quadrantSeedMatrices k).1
      (quadrantSeedMatrices k).2 (quadrantCoordinates k p) hp with ⟨v, N, h⟩ | ⟨u, M, h⟩
  · obtain ⟨b, hM, _⟩ := h.freeBasisPair (quadrantSeed_freeBasisPair k)
    refine ⟨b, 0, ?_⟩
    exact Subtype.ext (Subtype.ext hM)
  · obtain ⟨b, _, hN⟩ := h.freeBasisPair (quadrantSeed_freeBasisPair k)
    refine ⟨b, 1, ?_⟩
    exact Subtype.ext (Subtype.ext hN)

/-- An actual group automorphism transports genuine free-basis generators. -/
theorem TraceFreeBasisGenerator.map {g : modularTraceSubgroup}
    (hg : TraceFreeBasisGenerator g) (e : modularTraceSubgroup ≃* modularTraceSubgroup) :
    TraceFreeBasisGenerator (e g) := by
  obtain ⟨b, i, hi⟩ := hg
  exact ⟨b.map e, i, by rw [FreeGroupBasis.map_apply, hi]⟩

/-- The original-marked S-conjugate primitive holonomy is also a genuine
free-basis generator, without any assertion about simple curves. -/
theorem paperPrimitiveHolonomy_freeBasisGenerator (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    TraceFreeBasisGenerator (paperPrimitiveHolonomy k p hp) :=
  (quadrantPrimitiveTraceWord_freeBasisGenerator k p hp).map modularTraceSeedConjugation

end Markov
