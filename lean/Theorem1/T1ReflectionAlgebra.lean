import Markov.QuadrantSymmetry

/-! The literal trace-preserving matrix anti-automorphism corresponding to
swapping the two original lattice labels. No surface isometry is assumed. -/
namespace Markov

def t1_latticeSwap (p : ℤ × ℤ) : ℤ × ℤ := (p.2,p.1)

def t1_reflectMatrix (M : IntMatrixTwo) : IntMatrixTwo :=
  !![M 0 0, -(M 1 0); -(M 0 1), M 1 1]

theorem t1_latticeSwap_add (p q : ℤ × ℤ) :
    t1_latticeSwap (p+q) = t1_latticeSwap p+t1_latticeSwap q := rfl

theorem t1_reflectMatrix_mul (M N : IntMatrixTwo) :
    t1_reflectMatrix (M*N) = t1_reflectMatrix N * t1_reflectMatrix M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [t1_reflectMatrix,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem t1_reflectMatrix_trace (M : IntMatrixTwo) :
    (t1_reflectMatrix M).trace = M.trace := by
  simp [t1_reflectMatrix,Matrix.trace,Matrix.diag_apply,Fin.sum_univ_two]

theorem t1_reflectMatrix_adjugate (M : IntMatrixTwo) :
    t1_reflectMatrix M.adjugate = (t1_reflectMatrix M).adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [t1_reflectMatrix,Matrix.adjugate_fin_two]

def t1_reflectedQuadrant : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 3
  | 2 => 2
  | 3 => 1

theorem t1_reflectedQuadrant_directions (k : Fin 4) :
    (quadrantSeedDirections (t1_reflectedQuadrant k)).1 =
      t1_latticeSwap (quadrantSeedDirections k).2 ∧
    (quadrantSeedDirections (t1_reflectedQuadrant k)).2 =
      t1_latticeSwap (quadrantSeedDirections k).1 := by
  fin_cases k <;> decide

theorem t1_reflectedQuadrant_matrices (k : Fin 4) :
    (quadrantSeedMatrices (t1_reflectedQuadrant k)).1 =
      t1_reflectMatrix (quadrantSeedMatrices k).2 ∧
    (quadrantSeedMatrices (t1_reflectedQuadrant k)).2 =
      t1_reflectMatrix (quadrantSeedMatrices k).1 := by
  fin_cases k <;> decide

theorem t1_seededFarey_reflection
    {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey u0 v0 M0 N0 u v M N) :
    SeededFarey (t1_latticeSwap v0) (t1_latticeSwap u0)
      (t1_reflectMatrix N0) (t1_reflectMatrix M0)
      (t1_latticeSwap v) (t1_latticeSwap u) (t1_reflectMatrix N) (t1_reflectMatrix M) := by
  induction h with
  | seed => exact SeededFarey.seed
  | left _ ih =>
    simpa only [t1_latticeSwap_add,t1_reflectMatrix_mul,add_comm] using ih.right
  | right _ ih =>
    simpa only [t1_latticeSwap_add,t1_reflectMatrix_mul,add_comm] using ih.left

theorem t1_quadrantSeededFarey_reflection (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N) :
    SeededFarey (quadrantSeedDirections (t1_reflectedQuadrant k)).1
      (quadrantSeedDirections (t1_reflectedQuadrant k)).2
      (quadrantSeedMatrices (t1_reflectedQuadrant k)).1
      (quadrantSeedMatrices (t1_reflectedQuadrant k)).2
      (t1_latticeSwap v) (t1_latticeSwap u) (t1_reflectMatrix N) (t1_reflectMatrix M) := by
  rw [(t1_reflectedQuadrant_directions k).1,(t1_reflectedQuadrant_directions k).2,
    (t1_reflectedQuadrant_matrices k).1,(t1_reflectedQuadrant_matrices k).2]
  exact t1_seededFarey_reflection h

theorem t1_quadrantWordTrace_reflection {p : ℤ × ℤ} {t : ℤ}
    (h : QuadrantWordTrace p t) : QuadrantWordTrace (t1_latticeSwap p) t := by
  obtain ⟨k,u,v,M,N,hw,hp⟩ := h
  refine ⟨t1_reflectedQuadrant k,t1_latticeSwap v,t1_latticeSwap u,
    t1_reflectMatrix N,t1_reflectMatrix M,t1_quadrantSeededFarey_reflection k hw,?_⟩
  rcases hp with ⟨rfl,ht⟩ | ⟨rfl,ht⟩
  · exact Or.inr ⟨rfl,ht.trans (t1_reflectMatrix_trace M).symm⟩
  · exact Or.inl ⟨rfl,ht.trans (t1_reflectMatrix_trace N).symm⟩

end Markov
