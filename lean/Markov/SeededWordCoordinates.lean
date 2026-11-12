import Markov.PaperAbelianization
import Markov.QuadrantCoverage
import Markov.SeededFarey
import Markov.PrimitiveMetricLength

/-! Actual subgroup membership and algebraic abelianization coordinates of
the signed Farey matrix words. The trace seeds are inverses of the original
paper generators, so their literal coordinates are the negative labels.
No identification with singular homology or simple curves is assumed. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- A literal integer matrix word in the actual subgroup, with its actual
original-generator algebraic abelianization coordinates. -/
def PaperWordCoordinates (M : IntMatrixTwo) (u : ℤ × ℤ) : Prop :=
  ∃ g : modularTraceSubgroup, (g.val : IntMatrixTwo) = M ∧
    paperTraceAbelianizationCoordinates g = Multiplicative.ofAdd u

theorem PaperWordCoordinates.mul {M N : IntMatrixTwo} {u v : ℤ × ℤ}
    (hM : PaperWordCoordinates M u) (hN : PaperWordCoordinates N v) :
    PaperWordCoordinates (M * N) (u + v) := by
  obtain ⟨g, hg, hgu⟩ := hM
  obtain ⟨h, hh, hhv⟩ := hN
  refine ⟨g * h, ?_, ?_⟩
  · change ((g.val * h.val : SL(2, ℤ)) : IntMatrixTwo) = M * N
    rw [Matrix.SpecialLinearGroup.coe_mul, hg, hh]
  · rw [map_mul, hgu, hhv]
    rfl

theorem PaperWordCoordinates.inv {M : IntMatrixTwo} {u : ℤ × ℤ}
    (hM : PaperWordCoordinates M u) : PaperWordCoordinates M.adjugate (-u) := by
  obtain ⟨g, hg, hgu⟩ := hM
  refine ⟨g⁻¹, ?_, ?_⟩
  · change ((g.val⁻¹ : SL(2, ℤ)) : IntMatrixTwo) = M.adjugate
    rw [Matrix.SpecialLinearGroup.coe_inv, hg]
  · rw [map_inv, hgu]
    rfl

theorem modularGeneratorA_paperWordCoordinates :
    PaperWordCoordinates modularGeneratorA (-1, 0) := by
  refine ⟨(paperTraceFreeGroupBasis 0)⁻¹, ?_, ?_⟩
  · change (((paperTraceFreeGroupBasis 0 : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : IntMatrixTwo) = _
    rw [paperTraceFreeGroupBasis_zero, ← modularGeneratorASL_eq_paperGeneratorASL_inv]
    rfl
  · rw [map_inv, paperTraceAbelianizationCoordinates_basis_zero]
    rfl

theorem modularGeneratorB_paperWordCoordinates :
    PaperWordCoordinates modularGeneratorB (0, -1) := by
  refine ⟨(paperTraceFreeGroupBasis 1)⁻¹, ?_, ?_⟩
  · change (((paperTraceFreeGroupBasis 1 : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : IntMatrixTwo) = _
    rw [paperTraceFreeGroupBasis_one, ← modularGeneratorBSL_eq_paperGeneratorBSL_inv]
    rfl
  · rw [map_inv, paperTraceAbelianizationCoordinates_basis_one]
    rfl

/-- Actual matrix multiplication and actual group abelianization follow
the same labelled Farey moves, for any explicit additive label map. -/
theorem SeededFarey.paperWordCoordinates
    {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey u0 v0 M0 N0 u v M N)
    (F : (ℤ × ℤ) →+ (ℤ × ℤ))
    (hM : PaperWordCoordinates M0 (F u0)) (hN : PaperWordCoordinates N0 (F v0)) :
    PaperWordCoordinates M (F u) ∧ PaperWordCoordinates N (F v) := by
  induction h with
  | seed => exact ⟨hM, hN⟩
  | left _ ih => exact ⟨ih.1, by simpa only [map_add] using ih.1.mul ih.2⟩
  | right _ ih => exact ⟨by simpa only [map_add] using ih.1.mul ih.2, ih.2⟩

theorem quadrantSeed_paperWordCoordinates (k : Fin 4) :
    PaperWordCoordinates (quadrantSeedMatrices k).1 (-(quadrantSeedDirections k).1) ∧
      PaperWordCoordinates (quadrantSeedMatrices k).2 (-(quadrantSeedDirections k).2) := by
  have ha := modularGeneratorA_paperWordCoordinates
  have hb := modularGeneratorB_paperWordCoordinates
  have hai := ha.inv
  have hbi := hb.inv
  fin_cases k
  · exact ⟨ha, hb⟩
  · exact ⟨hb, hai⟩
  · exact ⟨hai, hbi⟩
  · exact ⟨hbi, ha⟩

theorem SeededFarey.quadrant_paperWordCoordinates
    {k : Fin 4} {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N) :
    PaperWordCoordinates M (-u) ∧ PaperWordCoordinates N (-v) := by
  let F : (ℤ × ℤ) →+ (ℤ × ℤ) :=
    { toFun := fun p => -p
      map_zero' := neg_zero
      map_add' := fun p q => neg_add p q }
  exact h.paperWordCoordinates F (quadrantSeed_paperWordCoordinates k).1
    (quadrantSeed_paperWordCoordinates k).2

/-- Every signed primitive label is carried by an actual matrix in the
actual subgroup, with its literal (negative) original-basis coordinates. -/
theorem primitive_exists_paperWordCoordinates (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    ∃ k : Fin 4, ∃ u v : ℤ × ℤ, ∃ M N : IntMatrixTwo,
      SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
        (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N ∧
      ((p = u ∧ PaperWordCoordinates M (-p)) ∨
        (p = v ∧ PaperWordCoordinates N (-p))) := by
  obtain ⟨k, u, v, M, N, h, hp'⟩ := primitive_exists_quadrantSeededFarey p hp
  refine ⟨k, u, v, M, N, h, ?_⟩
  rcases hp' with rfl | rfl
  · exact Or.inl ⟨rfl, h.quadrant_paperWordCoordinates.1⟩
  · exact Or.inr ⟨rfl, h.quadrant_paperWordCoordinates.2⟩

/-- The actual canonical primitive matrix, not merely an unspecified word
with the same trace, has the negative original-paper abelianization label. -/
theorem quadrantPrimitiveSeedMatrix_paperWordCoordinates (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    PaperWordCoordinates
      (primitiveSeedMatrix (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
        (quadrantCoordinates k p) hp) (-p) := by
  let F : (ℤ × ℤ) →+ (ℤ × ℤ) :=
    { toFun := fun a => -seededDirection (quadrantSeedDirections k).1
        (quadrantSeedDirections k).2 a
      map_zero' := by simp [seededDirection]
      map_add' := fun a b => by rw [seededDirection_add, neg_add] }
  have hM : PaperWordCoordinates (quadrantSeedMatrices k).1 (F (1, 0)) := by
    simpa only [F, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      (seededDirection_zero_one (quadrantSeedDirections k).1
        (quadrantSeedDirections k).2).1] using (quadrantSeed_paperWordCoordinates k).1
  have hN : PaperWordCoordinates (quadrantSeedMatrices k).2 (F (0, 1)) := by
    simpa only [F, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      (seededDirection_zero_one (quadrantSeedDirections k).1
        (quadrantSeedDirections k).2).2] using (quadrantSeed_paperWordCoordinates k).2
  rcases primitiveSeedMatrix_spec (quadrantSeedMatrices k).1
      (quadrantSeedMatrices k).2 (quadrantCoordinates k p) hp with ⟨v, N, h⟩ | ⟨u, M, h⟩
  · simpa only [F, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      quadrantCoordinates_reconstruct] using (h.paperWordCoordinates F hM hN).1
  · simpa only [F, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      quadrantCoordinates_reconstruct] using (h.paperWordCoordinates F hM hN).2

theorem quadrantPrimitiveSeedHolonomy_mem (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    primitiveSeedHolonomy (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
      (quadrantSeed_positiveFrickePair k) (quadrantCoordinates k p) hp ∈
        modularTraceSubgroup := by
  obtain ⟨g, hg, _⟩ := quadrantPrimitiveSeedMatrix_paperWordCoordinates k p hp
  have he : g.val = primitiveSeedHolonomy (quadrantSeedMatrices k).1
      (quadrantSeedMatrices k).2 (quadrantSeed_positiveFrickePair k)
      (quadrantCoordinates k p) hp := Subtype.ext hg
  exact he ▸ g.property

/-- The canonical signed trace word as an actual element of the actual
acting subgroup, with membership now proved from its word construction. -/
def quadrantPrimitiveTraceWord (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) : modularTraceSubgroup :=
  ⟨primitiveSeedHolonomy (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
    (quadrantSeed_positiveFrickePair k) (quadrantCoordinates k p) hp,
      quadrantPrimitiveSeedHolonomy_mem k p hp⟩

theorem quadrantPrimitiveTraceWord_coordinates (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    paperTraceAbelianizationCoordinates (quadrantPrimitiveTraceWord k p hp) =
      Multiplicative.ofAdd (-p) := by
  obtain ⟨g, hg, hcoords⟩ := quadrantPrimitiveSeedMatrix_paperWordCoordinates k p hp
  have he : quadrantPrimitiveTraceWord k p hp = g :=
    Subtype.ext (Subtype.ext hg.symm)
  rw [he]
  exact hcoords

end Markov
