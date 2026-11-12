import Markov.SeededFarey
import Markov.QuadrantSeeds

/-! Central negation of the two direction coordinates preserves the
matrix-word trace and the numerical length assignment. -/

namespace Markov

/-- Transposed adjugation is multiplicative and trace-preserving in dimension two. -/
def antipodalMatrix (M : IntMatrixTwo) : IntMatrixTwo := M.adjugate.transpose

theorem antipodalMatrix_mul (M N : IntMatrixTwo) :
    antipodalMatrix (M * N) = antipodalMatrix M * antipodalMatrix N := by
  simp only [antipodalMatrix, Matrix.adjugate_mul_distrib, Matrix.transpose_mul]

theorem antipodalMatrix_trace (M : IntMatrixTwo) : (antipodalMatrix M).trace = M.trace := by
  rw [antipodalMatrix, Matrix.trace_transpose]
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  simp
  ring

theorem antipodalMatrix_involutive (M : IntMatrixTwo) :
    antipodalMatrix (antipodalMatrix M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antipodalMatrix, Matrix.adjugate_fin_two, Matrix.transpose_apply]

/-- The quadrant opposite `k` in counterclockwise order. -/
def antipodalQuadrant (k : Fin 4) : Fin 4 :=
  ⟨(k.val + 2) % 4, Nat.mod_lt _ (by decide)⟩

theorem antipodalQuadrant_involutive (k : Fin 4) :
    antipodalQuadrant (antipodalQuadrant k) = k := by
  fin_cases k <;> decide

theorem quadrantSeedDirections_antipodal (k : Fin 4) :
    (quadrantSeedDirections (antipodalQuadrant k)).1 = -(quadrantSeedDirections k).1 ∧
    (quadrantSeedDirections (antipodalQuadrant k)).2 = -(quadrantSeedDirections k).2 := by
  fin_cases k <;> norm_num [antipodalQuadrant, quadrantSeedDirections]

theorem quadrantSeedMatrices_antipodal (k : Fin 4) :
    (quadrantSeedMatrices (antipodalQuadrant k)).1 = antipodalMatrix (quadrantSeedMatrices k).1 ∧
    (quadrantSeedMatrices (antipodalQuadrant k)).2 = antipodalMatrix (quadrantSeedMatrices k).2 := by
  fin_cases k <;> constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [antipodalQuadrant, quadrantSeedMatrices, antipodalMatrix,
      modularGeneratorA, modularGeneratorB, Matrix.adjugate_fin_two, Matrix.transpose_apply]

/-- Central negation of the direction labels transports the same actual
matrix word by transposed adjugation. -/
theorem SeededFarey.antipodal {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey u0 v0 M0 N0 u v M N) :
    SeededFarey (-u0) (-v0) (antipodalMatrix M0) (antipodalMatrix N0)
      (-u) (-v) (antipodalMatrix M) (antipodalMatrix N) := by
  induction h with
  | seed => exact SeededFarey.seed
  | left _ ih => simpa only [neg_add, antipodalMatrix_mul] using ih.left
  | right _ ih => simpa only [neg_add, antipodalMatrix_mul] using ih.right

/-- The four concrete seeds are paired by the antipodal transport. -/
theorem SeededFarey.quadrant_antipodal (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N) :
    SeededFarey (quadrantSeedDirections (antipodalQuadrant k)).1
      (quadrantSeedDirections (antipodalQuadrant k)).2
      (quadrantSeedMatrices (antipodalQuadrant k)).1
      (quadrantSeedMatrices (antipodalQuadrant k)).2
      (-u) (-v) (antipodalMatrix M) (antipodalMatrix N) := by
  rw [(quadrantSeedDirections_antipodal k).1, (quadrantSeedDirections_antipodal k).2,
    (quadrantSeedMatrices_antipodal k).1, (quadrantSeedMatrices_antipodal k).2]
  exact h.antipodal

/-- A numerical primitive candidate length is preserved by the antipodal map. -/
theorem antipodalMatrix_length (M : IntMatrixTwo) :
    2 * Real.arcosh (((antipodalMatrix M).trace : ℝ) / 2) =
      2 * Real.arcosh ((M.trace : ℝ) / 2) := by
  rw [antipodalMatrix_trace]

/-- The actual trace attached to a labelled endpoint of a quadrant word. -/
def QuadrantWordTrace (p : ℤ × ℤ) (t : ℤ) : Prop :=
  ∃ (k : Fin 4) (u v : ℤ × ℤ) (M N : IntMatrixTwo),
    SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N ∧
    ((p = u ∧ t = M.trace) ∨ (p = v ∧ t = N.trace))

/-- Central negation preserves the actual candidate trace, including
when a direction occurs as either endpoint. -/
theorem quadrantWordTrace_neg {p : ℤ × ℤ} {t : ℤ}
    (h : QuadrantWordTrace p t) : QuadrantWordTrace (-p) t := by
  obtain ⟨k, u, v, M, N, hw, hp⟩ := h
  refine ⟨antipodalQuadrant k, -u, -v, antipodalMatrix M, antipodalMatrix N,
    hw.quadrant_antipodal k, ?_⟩
  rcases hp with ⟨rfl, ht⟩ | ⟨rfl, ht⟩
  · exact Or.inl ⟨rfl, ht.trans (antipodalMatrix_trace M).symm⟩
  · exact Or.inr ⟨rfl, ht.trans (antipodalMatrix_trace N).symm⟩

theorem quadrantWordTrace_neg_iff (p : ℤ × ℤ) (t : ℤ) :
    QuadrantWordTrace (-p) t ↔ QuadrantWordTrace p t := by
  constructor
  · intro h
    simpa only [neg_neg] using quadrantWordTrace_neg h
  · exact quadrantWordTrace_neg

/-- Candidate lengths expressed by their actual quadrant trace. No norm
interpretation or global uniqueness of quadrant traces is assumed. -/
def QuadrantWordLength (p : ℤ × ℤ) (ℓ : ℝ) : Prop :=
  ∃ t : ℤ, QuadrantWordTrace p t ∧ ℓ = 2 * Real.arcosh ((t : ℝ) / 2)

theorem quadrantWordLength_neg_iff (p : ℤ × ℤ) (ℓ : ℝ) :
    QuadrantWordLength (-p) ℓ ↔ QuadrantWordLength p ℓ := by
  simp only [QuadrantWordLength, quadrantWordTrace_neg_iff]

end Markov
