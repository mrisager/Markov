import Markov.OriginalLinearFareyWitnesses
import Markov.SeededGeometricRealization

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- Actual signed linear and nonabelian pair witnesses at both matrix labels. -/
def TraceLinearBasisPair (u v : ℤ × ℤ) (M N : IntMatrixTwo) : Prop :=
  ∃ g h : modularTraceSubgroup, OriginalPairLinearlyRealized u v g h ∧
    (g.val : IntMatrixTwo) = M ∧ (h.val : IntMatrixTwo) = N

/-- The four literal signed seeds have actual enriched linear witnesses. -/
theorem quadrantSeed_linearBasisPair (k : Fin 4) :
    TraceLinearBasisPair (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 := by
  let b := paperTraceFreeGroupBasis
  have ha : (b 0 : SL(2, ℤ)) = paperGeneratorASL := paperTraceFreeGroupBasis_zero
  have hb : (b 1 : SL(2, ℤ)) = paperGeneratorBSL := paperTraceFreeGroupBasis_one
  have hp : OriginalPairLinearlyRealized (-1,0) (0,-1) (b 0) (b 1) := originalPairLinearlyRealized_basis
  fin_cases k
  · refine ⟨(b 0)⁻¹, (b 1)⁻¹, ?_, ?_, ?_⟩
    · simpa [quadrantSeedDirections] using hp.invert_first.invert_second
    · change (((b 0 : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : IntMatrixTwo) = modularGeneratorA
      rw [ha, ← modularGeneratorASL_eq_paperGeneratorASL_inv]
      rfl
    · change (((b 1 : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : IntMatrixTwo) = modularGeneratorB
      rw [hb, ← modularGeneratorBSL_eq_paperGeneratorBSL_inv]
      rfl
  · refine ⟨(b 1)⁻¹, b 0, ?_, ?_, ?_⟩
    · simpa [quadrantSeedDirections] using hp.invert_second.swap
    · change (((b 1 : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : IntMatrixTwo) = modularGeneratorB
      rw [hb, ← modularGeneratorBSL_eq_paperGeneratorBSL_inv]
      rfl
    · change ((b 0).val : IntMatrixTwo) = modularGeneratorA.adjugate
      rw [ha]
      norm_num [paperGeneratorASL, paperGeneratorA, modularGeneratorA, Matrix.adjugate_fin_two]
  · refine ⟨b 0, b 1, ?_, ?_, ?_⟩
    · simpa [quadrantSeedDirections] using hp
    · change ((b 0).val : IntMatrixTwo) = modularGeneratorA.adjugate
      rw [ha]
      norm_num [paperGeneratorASL, paperGeneratorA, modularGeneratorA, Matrix.adjugate_fin_two]
    · change ((b 1).val : IntMatrixTwo) = modularGeneratorB.adjugate
      rw [hb]
      norm_num [paperGeneratorBSL, paperGeneratorB, modularGeneratorB, Matrix.adjugate_fin_two]
  · refine ⟨b 1, (b 0)⁻¹, ?_, ?_, ?_⟩
    · simpa [quadrantSeedDirections] using hp.invert_first.swap
    · change ((b 1).val : IntMatrixTwo) = modularGeneratorB.adjugate
      rw [hb]
      norm_num [paperGeneratorBSL, paperGeneratorB, modularGeneratorB, Matrix.adjugate_fin_two]
    · change (((b 0 : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : IntMatrixTwo) = modularGeneratorA
      rw [ha, ← modularGeneratorASL_eq_paperGeneratorASL_inv]
      rfl

/-- Actual seeded Farey induction preserves the literal linear map and
both exact original nonabelian generator images together. -/
theorem SeededFarey.linearBasisPair {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey u0 v0 M0 N0 u v M N) (h0 : TraceLinearBasisPair u0 v0 M0 N0) :
    TraceLinearBasisPair u v M N := by
  induction h with
  | seed => exact h0
  | left _ ih =>
    rcases ih with ⟨g, h, hp, hM, hN⟩
    refine ⟨g, g*h, hp.left, hM, ?_⟩
    change (g.val : IntMatrixTwo) * (h.val : IntMatrixTwo) = _
    rw [hM, hN]
  | right _ ih =>
    rcases ih with ⟨g, h, hp, hM, hN⟩
    refine ⟨g*h, h, hp.right, ?_, hN⟩
    change (g.val : IntMatrixTwo) * (h.val : IntMatrixTwo) = _
    rw [hM, hN]

/-- Relabel an actual coordinate word by the literal quadrant columns,
retaining its two actual integer matrices exactly. -/
theorem SeededFarey.to_quadrant_directions
    {u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey (1,0) (0,1) M0 N0 u v M N) (k : Fin 4) :
    SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2 M0 N0
      (seededDirection (quadrantSeedDirections k).1 (quadrantSeedDirections k).2 u)
      (seededDirection (quadrantSeedDirections k).1 (quadrantSeedDirections k).2 v) M N := by
  induction h with
  | seed =>
    simpa only [(seededDirection_zero_one (quadrantSeedDirections k).1
        (quadrantSeedDirections k).2).1,
      (seededDirection_zero_one (quadrantSeedDirections k).1
        (quadrantSeedDirections k).2).2] using
      (SeededFarey.seed (u0 := (quadrantSeedDirections k).1)
        (v0 := (quadrantSeedDirections k).2) (M0 := M0) (N0 := N0))
  | left _ ih => simpa only [seededDirection_add] using ih.left
  | right _ ih => simpa only [seededDirection_add] using ih.right

/-- Every literal raw canonical word occurs in an actual determinant-one
linear/nonabelian pair at its exact original signed lattice label. -/
theorem quadrantPrimitiveTraceWord_linear_pair (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    ∃ (u v : ℤ × ℤ) (g h : modularTraceSubgroup),
      intDet u v = 1 ∧ OriginalPairLinearlyRealized u v g h ∧
      ((u = p ∧ g = quadrantPrimitiveTraceWord k p hp) ∨
        (v = p ∧ h = quadrantPrimitiveTraceWord k p hp)) := by
  rcases primitiveSeedMatrix_spec (quadrantSeedMatrices k).1
      (quadrantSeedMatrices k).2 (quadrantCoordinates k p) hp with ⟨v, N, h⟩ | ⟨u, M, h⟩
  · have hq := h.to_quadrant_directions k
    rw [quadrantCoordinates_reconstruct] at hq
    rcases hq.linearBasisPair (quadrantSeed_linearBasisPair k) with ⟨g, h, hpair, hM, _⟩
    have hd : intDet p (seededDirection (quadrantSeedDirections k).1
        (quadrantSeedDirections k).2 v) = 1 := by
      simpa only [quadrantSeed_det_eq_one] using hq.det_eq_seed
    have he : g = quadrantPrimitiveTraceWord k p hp := Subtype.ext (Subtype.ext hM)
    exact ⟨_, _, g, h, hd, hpair, Or.inl ⟨rfl, he⟩⟩
  · have hq := h.to_quadrant_directions k
    rw [quadrantCoordinates_reconstruct] at hq
    rcases hq.linearBasisPair (quadrantSeed_linearBasisPair k) with ⟨g, h, hpair, _, hN⟩
    have hd : intDet (seededDirection (quadrantSeedDirections k).1
        (quadrantSeedDirections k).2 u) p = 1 := by
      simpa only [quadrantSeed_det_eq_one] using hq.det_eq_seed
    have he : h = quadrantPrimitiveTraceWord k p hp := Subtype.ext (Subtype.ext hN)
    exact ⟨_, _, g, h, hd, hpair, Or.inr ⟨rfl, he⟩⟩

end Markov
