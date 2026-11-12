import Markov.SeedCanonical
import Markov.FareyRefinement

/-! Replace the seed matrices on the existing finite Farey combinatorics.
Every evaluation carries a genuine seeded matrix-word witness; uniqueness
makes the result independent of the existential word transport. -/

noncomputable section

namespace Markov

private theorem seedEvaluation_direction (p : ℤ × ℤ) :
    seededDirection (1, 0) (0, 1) p = p := by
  ext <;> simp [seededDirection]

/-- Every old combinatorial edge can be evaluated using any actual seed pair. -/
theorem exists_seedEvaluation (M0 N0 : IntMatrixTwo) (e : FareyEdge) :
    ∃ PQ : IntMatrixTwo × IntMatrixTwo,
      SeededFarey (1, 0) (0, 1) M0 N0 e.u e.v PQ.1 PQ.2 := by
  obtain ⟨P, Q, h⟩ := e.holonomy.to_seeded (1, 0) (0, 1) M0 N0
  exact ⟨(P, Q), by simpa only [seedEvaluation_direction] using h⟩

/-- Actual matrix values on the same Farey edges with a replacement seed. -/
def seedEvaluation (M0 N0 : IntMatrixTwo) (e : FareyEdge) : IntMatrixTwo × IntMatrixTwo :=
  Classical.choose (exists_seedEvaluation M0 N0 e)

theorem seedEvaluation_spec (M0 N0 : IntMatrixTwo) (e : FareyEdge) :
    SeededFarey (1, 0) (0, 1) M0 N0 e.u e.v
      (seedEvaluation M0 N0 e).1 (seedEvaluation M0 N0 e).2 :=
  Classical.choose_spec (exists_seedEvaluation M0 N0 e)

/-- The actual root evaluates to the specified seed pair. -/
theorem seedEvaluation_seed (M0 N0 : IntMatrixTwo) :
    seedEvaluation M0 N0 FareyEdge.seed = (M0, N0) := by
  have h := (seedEvaluation_spec M0 N0 FareyEdge.seed).coordinate_matrices_unique
    (SeededFarey.seed (u0 := (1, 0)) (v0 := (0, 1)) (M0 := M0) (N0 := N0))
  exact Prod.ext h.1 h.2

/-- Left refinement performs the actual matrix multiplication. -/
theorem seedEvaluation_left (M0 N0 : IntMatrixTwo) (e : FareyEdge) :
    seedEvaluation M0 N0 e.left =
      ((seedEvaluation M0 N0 e).1,
        (seedEvaluation M0 N0 e).1 * (seedEvaluation M0 N0 e).2) := by
  have h := (seedEvaluation_spec M0 N0 e.left).coordinate_matrices_unique
    (seedEvaluation_spec M0 N0 e).left
  exact Prod.ext h.1 h.2

/-- Right refinement performs the complementary actual multiplication. -/
theorem seedEvaluation_right (M0 N0 : IntMatrixTwo) (e : FareyEdge) :
    seedEvaluation M0 N0 e.right =
      ((seedEvaluation M0 N0 e).1 * (seedEvaluation M0 N0 e).2,
        (seedEvaluation M0 N0 e).2) := by
  have h := (seedEvaluation_spec M0 N0 e.right).coordinate_matrices_unique
    (seedEvaluation_spec M0 N0 e).right
  exact Prod.ext h.1 h.2

/-- All of the arithmetic seed conditions propagate to the actual evaluated
pair; no geometric identification is assumed. -/
theorem seedEvaluation_positiveFrickePair (M0 N0 : IntMatrixTwo)
    (hp : PositiveFrickePair M0 N0) (e : FareyEdge) :
    PositiveFrickePair (seedEvaluation M0 N0 e).1 (seedEvaluation M0 N0 e).2 :=
  (seedEvaluation_spec M0 N0 e).positiveFrickePair hp

/-- Consecutive evaluated edges carry the same actual matrix at their
shared endpoint, even with a replacement seed. -/
theorem seedEvaluation_adjacent_endpoint (M0 N0 : IntMatrixTwo) (n : ℕ)
    (a b : FareyEdge) (hadj : FareyAdjacent a b (fareyFrontier n)) :
    (seedEvaluation M0 N0 a).2 = (seedEvaluation M0 N0 b).1 := by
  obtain ⟨u, v, M, N, k, _, hav, hbu, _, _⟩ := fareyFrontier_adjacent_birth n a b hadj
  have he : a.v = b.u := hav.trans hbu.symm
  have ha := seedEvaluation_spec M0 N0 a
  rw [he] at ha
  exact ((seedEvaluation_spec M0 N0 b).coordinate_cross_matrix_unique ha).symm

private theorem seedEvaluation_oldWitness {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) :
    SeededFarey (1, 0) (0, 1) modularGeneratorA modularGeneratorB u v M N := by
  induction h with
  | seed => exact SeededFarey.seed
  | left _ ih => exact ih.left
  | right _ ih => exact ih.right

/-- Evaluation at the original seed recovers the already checked concrete
matrices, not merely their traces. -/
theorem seedEvaluation_original (e : FareyEdge) :
    seedEvaluation modularGeneratorA modularGeneratorB e = (e.M, e.N) := by
  have h := (seedEvaluation_spec modularGeneratorA modularGeneratorB e).coordinate_matrices_unique
    (seedEvaluation_oldWitness e.holonomy)
  exact Prod.ext h.1 h.2

end Markov
