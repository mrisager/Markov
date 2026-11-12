import Markov.OriginalGeometricRealization
import Markov.SeededFreeBases

/-! Actual existential homeomorphism witnesses for the literal signed Farey
matrix words. The canonical result concerns raw words in the original marking;
it does not identify a forward projected axis class without its required reversal. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- A literal group element is an actual homeomorphism-and-connector image of
one of the two original generators. This is an explicit existential witness. -/
def OriginalGeometricGenerator (g : modularTraceSubgroup) : Prop :=
  ∃ (f : ModularTraceQuotient ≃ₜ ModularTraceQuotient)
    (c : Path paperGeneratorCenterPoint (f paperGeneratorCenterPoint)) (i : Fin 2),
      originalMarkedHomeomorphEquiv f c (paperTraceFreeGroupBasis i) = g

/-- The first member of an actually realized pair has actual generator witnesses. -/
theorem OriginalPairGeometricallyRealized.first {g h : modularTraceSubgroup}
    (hp : OriginalPairGeometricallyRealized g h) : OriginalGeometricGenerator g := by
  rcases hp with ⟨f, c, hA, _⟩
  exact ⟨f, c, 0, hA⟩

/-- The second member has the same actual homeomorphism and connector witnesses. -/
theorem OriginalPairGeometricallyRealized.second {g h : modularTraceSubgroup}
    (hp : OriginalPairGeometricallyRealized g h) : OriginalGeometricGenerator h := by
  rcases hp with ⟨f, c, _, hB⟩
  exact ⟨f, c, 1, hB⟩

/-- Literal integral matrices are an actual geometrically realized original-generator pair. -/
def TraceGeometricBasisPair (M N : IntMatrixTwo) : Prop :=
  ∃ g h : modularTraceSubgroup, OriginalPairGeometricallyRealized g h ∧
    (g.val : IntMatrixTwo) = M ∧ (h.val : IntMatrixTwo) = N

/-- Each actual signed quadrant seed has actual surface-homeomorphism witnesses,
constructed from identity, coordinate swaps and coordinate reflections. -/
theorem quadrantSeed_geometricBasisPair (k : Fin 4) :
    TraceGeometricBasisPair (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 := by
  let b := paperTraceFreeGroupBasis
  have ha : (b 0 : SL(2, ℤ)) = paperGeneratorASL := paperTraceFreeGroupBasis_zero
  have hb : (b 1 : SL(2, ℤ)) = paperGeneratorBSL := paperTraceFreeGroupBasis_one
  have hp : OriginalPairGeometricallyRealized (b 0) (b 1) := originalPairGeometricallyRealized_basis
  fin_cases k
  · refine ⟨(b 0)⁻¹, (b 1)⁻¹, hp.invert_first.invert_second, ?_, ?_⟩
    · change (((b 0 : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : IntMatrixTwo) = modularGeneratorA
      rw [ha, ← modularGeneratorASL_eq_paperGeneratorASL_inv]
      rfl
    · change (((b 1 : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : IntMatrixTwo) = modularGeneratorB
      rw [hb, ← modularGeneratorBSL_eq_paperGeneratorBSL_inv]
      rfl
  · refine ⟨(b 1)⁻¹, b 0, hp.invert_second.swap, ?_, ?_⟩
    · change (((b 1 : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : IntMatrixTwo) = modularGeneratorB
      rw [hb, ← modularGeneratorBSL_eq_paperGeneratorBSL_inv]
      rfl
    · change ((b 0).val : IntMatrixTwo) = modularGeneratorA.adjugate
      rw [ha]
      norm_num [paperGeneratorASL, paperGeneratorA, modularGeneratorA, Matrix.adjugate_fin_two]
  · refine ⟨b 0, b 1, hp, ?_, ?_⟩
    · change ((b 0).val : IntMatrixTwo) = modularGeneratorA.adjugate
      rw [ha]
      norm_num [paperGeneratorASL, paperGeneratorA, modularGeneratorA, Matrix.adjugate_fin_two]
    · change ((b 1).val : IntMatrixTwo) = modularGeneratorB.adjugate
      rw [hb]
      norm_num [paperGeneratorBSL, paperGeneratorB, modularGeneratorB, Matrix.adjugate_fin_two]
  · refine ⟨b 1, (b 0)⁻¹, hp.invert_first.swap, ?_, ?_⟩
    · change ((b 1).val : IntMatrixTwo) = modularGeneratorB.adjugate
      rw [hb]
      norm_num [paperGeneratorBSL, paperGeneratorB, modularGeneratorB, Matrix.adjugate_fin_two]
    · change (((b 0 : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : IntMatrixTwo) = modularGeneratorA
      rw [ha, ← modularGeneratorASL_eq_paperGeneratorASL_inv]
      rfl

/-- Every actual Farey matrix move constructs new actual homeomorphism witnesses. -/
theorem SeededFarey.geometricBasisPair {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey u0 v0 M0 N0 u v M N) (h0 : TraceGeometricBasisPair M0 N0) :
    TraceGeometricBasisPair M N := by
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

/-- All actual signed-quadrant Farey pairs have actual geometric witnesses. -/
theorem SeededFarey.quadrant_geometricBasisPair {k : Fin 4} {u v : ℤ × ℤ}
    {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N) :
    TraceGeometricBasisPair M N :=
  h.geometricBasisPair (quadrantSeed_geometricBasisPair k)

/-- Every literal raw signed canonical primitive word is the exact nonabelian
image of an original generator under an actual surface homeomorphism and connector.
No H1-to-pi1 or simple/free-homotopy classification is used. -/
theorem quadrantPrimitiveTraceWord_geometricGenerator (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    OriginalGeometricGenerator (quadrantPrimitiveTraceWord k p hp) := by
  rcases primitiveSeedMatrix_spec (quadrantSeedMatrices k).1
      (quadrantSeedMatrices k).2 (quadrantCoordinates k p) hp with ⟨v, N, h⟩ | ⟨u, M, h⟩
  · rcases h.geometricBasisPair (quadrantSeed_geometricBasisPair k) with ⟨g, h, hpair, hM, _⟩
    have he : g = quadrantPrimitiveTraceWord k p hp := Subtype.ext (Subtype.ext hM)
    rw [← he]
    exact hpair.first
  · rcases h.geometricBasisPair (quadrantSeed_geometricBasisPair k) with ⟨g, h, hpair, _, hN⟩
    have he : h = quadrantPrimitiveTraceWord k p hp := Subtype.ext (Subtype.ext hN)
    rw [← he]
    exact hpair.second

end Markov
