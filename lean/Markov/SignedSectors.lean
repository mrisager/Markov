import Markov.QuadrantCoverage
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Eight actual signed coordinate permutations reduce directions to
`0 ≤ q ≤ p`. These are changes of coordinates only. In particular, no
single-coordinate reflection symmetry of the trace norm is asserted. -/

noncomputable section
namespace Markov

/-- The four quadrant coordinate rotations followed by their coordinate swaps. -/
def signedPairCoordinates {R : Type*} [Neg R] : Fin 8 → (R × R) → (R × R)
  | 0, p => p
  | 1, p => (p.2, -p.1)
  | 2, p => (-p.1, -p.2)
  | 3, p => (-p.2, p.1)
  | 4, p => (p.2, p.1)
  | 5, p => (-p.1, p.2)
  | 6, p => (-p.2, -p.1)
  | 7, p => (p.1, -p.2)

def signedSectorCoordinates : Fin 8 → (ℤ × ℤ) → (ℤ × ℤ) := signedPairCoordinates

/-- Index of the inverse signed permutation. -/
def signedSectorInverse : Fin 8 → Fin 8
  | 0 => 0
  | 1 => 3
  | 2 => 2
  | 3 => 1
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7

@[simp] theorem signedSectorInverse_involutive (k : Fin 8) :
    signedSectorInverse (signedSectorInverse k) = k := by
  fin_cases k <;> rfl

@[simp] theorem signedPairCoordinates_inverse {R : Type*} [AddGroup R]
    (k : Fin 8) (p : R × R) :
    signedPairCoordinates (signedSectorInverse k) (signedPairCoordinates k p) = p := by
  fin_cases k <;> ext <;> simp [signedPairCoordinates, signedSectorInverse]

@[simp] theorem signedSectorCoordinates_inverse (k : Fin 8) (p : ℤ × ℤ) :
    signedSectorCoordinates (signedSectorInverse k) (signedSectorCoordinates k p) = p :=
  signedPairCoordinates_inverse k p

theorem signedSectorCoordinates_injective (k : Fin 8) :
    Function.Injective (signedSectorCoordinates k) := by
  intro p q h
  have hh := congrArg (signedSectorCoordinates (signedSectorInverse k)) h
  simpa only [signedSectorCoordinates_inverse] using hh

@[simp] theorem signedSectorCoordinates_zero (k : Fin 8) :
    signedSectorCoordinates k (0, 0) = (0, 0) := by
  fin_cases k <;> norm_num [signedSectorCoordinates, signedPairCoordinates]

@[simp] theorem signedSectorCoordinates_add (k : Fin 8) (u v : ℤ × ℤ) :
    signedSectorCoordinates k (u + v) =
      signedSectorCoordinates k u + signedSectorCoordinates k v := by
  fin_cases k <;> ext <;>
    simp [signedSectorCoordinates, signedPairCoordinates, add_comm]

theorem signedSectorCoordinates_ne_zero (k : Fin 8) (p : ℤ × ℤ) :
    signedSectorCoordinates k p ≠ (0, 0) ↔ p ≠ (0, 0) := by
  constructor
  · intro h hp
    exact h (hp ▸ signedSectorCoordinates_zero k)
  · intro h hp
    apply h
    apply signedSectorCoordinates_injective k
    simpa only [signedSectorCoordinates_zero] using hp

@[simp] theorem signedSectorCoordinates_height (k : Fin 8) (p : ℤ × ℤ) :
    intHeight (signedSectorCoordinates k p) = intHeight p := by
  fin_cases k <;> simp [signedSectorCoordinates, signedPairCoordinates, intHeight, max_comm]

@[simp] theorem signedSectorCoordinates_euclidean (k : Fin 8) (p : ℤ × ℤ) :
    intEuclidean (signedSectorCoordinates k p) = intEuclidean p := by
  fin_cases k <;>
    simp [signedSectorCoordinates, signedPairCoordinates, intEuclidean, add_comm]

/-- The sign of the determinant is allowed to change. -/
theorem signedSectorCoordinates_abs_det (k : Fin 8) (u v : ℤ × ℤ) :
    |intDet (signedSectorCoordinates k u) (signedSectorCoordinates k v)| = |intDet u v| := by
  fin_cases k <;>
    simp [signedSectorCoordinates, signedPairCoordinates, intDet, abs_sub_comm] <;> ring_nf
  all_goals
    rw [show -(u.1 * v.2) + u.2 * v.1 = -(u.1 * v.2 - u.2 * v.1) by ring, abs_neg]

theorem signedSectorCoordinates_coprime (k : Fin 8) (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    IsCoprime (signedSectorCoordinates k p).1 (signedSectorCoordinates k p).2 := by
  fin_cases k
  · exact hp
  · exact hp.symm.neg_right
  · exact hp.neg_neg
  · exact hp.symm.neg_left
  · exact hp.symm
  · exact hp.neg_left
  · exact hp.symm.neg_neg
  · exact hp.neg_right

theorem signedSectorCoordinates_coprime_iff (k : Fin 8) (p : ℤ × ℤ) :
    IsCoprime (signedSectorCoordinates k p).1 (signedSectorCoordinates k p).2 ↔
      IsCoprime p.1 p.2 := by
  constructor
  · intro h
    simpa only [signedSectorCoordinates_inverse] using
      signedSectorCoordinates_coprime (signedSectorInverse k) (signedSectorCoordinates k p) h
  · exact signedSectorCoordinates_coprime k p

/-- A closed sector is the inverse image of the canonical slope interval. -/
def InSignedSector (k : Fin 8) (p : ℤ × ℤ) : Prop :=
  0 ≤ (signedSectorCoordinates k p).2 ∧
    (signedSectorCoordinates k p).2 ≤ (signedSectorCoordinates k p).1

/-- The eight closed coordinate sectors cover every integral vector. -/
theorem exists_signedSector (p : ℤ × ℤ) : ∃ k : Fin 8, InSignedSector k p := by
  obtain ⟨k, hx, hy⟩ := exists_nonnegative_quadrantCoordinates p
  by_cases hxy : (quadrantCoordinates k p).2 ≤ (quadrantCoordinates k p).1
  · fin_cases k
    · exact ⟨0, hy, hxy⟩
    · exact ⟨1, hy, hxy⟩
    · exact ⟨2, hy, hxy⟩
    · exact ⟨3, hy, hxy⟩
  · have hyx := le_of_lt (lt_of_not_ge hxy)
    fin_cases k
    · exact ⟨4, hx, hyx⟩
    · exact ⟨5, hx, hyx⟩
    · exact ⟨6, hx, hyx⟩
    · exact ⟨7, hx, hyx⟩

theorem InSignedSector.first_pos (k : Fin 8) (p : ℤ × ℤ)
    (h : InSignedSector k p) (hp : p ≠ (0, 0)) :
    0 < (signedSectorCoordinates k p).1 := by
  have hn := (signedSectorCoordinates_ne_zero k p).2 hp
  rcases h with ⟨hq, hqp⟩
  by_contra hh
  apply hn
  ext <;> dsimp <;> omega

/-- Infinity height is the positive first canonical coordinate in a sector. -/
theorem InSignedSector.height_eq_first (k : Fin 8) (p : ℤ × ℤ)
    (h : InSignedSector k p) :
    intHeight p = ((signedSectorCoordinates k p).1 : ℝ) := by
  have hq : (0 : ℝ) ≤ (signedSectorCoordinates k p).2 := by exact_mod_cast h.1
  have hqp : ((signedSectorCoordinates k p).2 : ℝ) ≤ (signedSectorCoordinates k p).1 := by
    exact_mod_cast h.2
  rw [← signedSectorCoordinates_height k p, intHeight,
    abs_of_nonneg (hq.trans hqp), abs_of_nonneg hq, max_eq_left hqp]

theorem InSignedSector.add (k : Fin 8) (u v : ℤ × ℤ)
    (hu : InSignedSector k u) (hv : InSignedSector k v) : InSignedSector k (u + v) := by
  rcases hu with ⟨huq, hupq⟩
  rcases hv with ⟨hvq, hvpq⟩
  unfold InSignedSector
  rw [signedSectorCoordinates_add]
  exact ⟨add_nonneg huq hvq, add_le_add hupq hvpq⟩

/-- A cutoff expressed with infinity heights has exactly the usual sum of
denominators after a common-sector coordinate transformation. -/
theorem InSignedSector.height_add (k : Fin 8) (u v : ℤ × ℤ)
    (hu : InSignedSector k u) (hv : InSignedSector k v) :
    intHeight (u + v) = intHeight u + intHeight v := by
  rw [(hu.add k u v hv).height_eq_first k (u + v),
    hu.height_eq_first k u, hv.height_eq_first k v, signedSectorCoordinates_add]
  simp only [Prod.fst_add, Int.cast_add]

/-- Every nonzero integral vector has canonical sector coordinates with
strictly positive denominator. -/
theorem exists_positive_signedSectorCoordinates (p : ℤ × ℤ) (hp : p ≠ (0, 0)) :
    ∃ k : Fin 8, 0 < (signedSectorCoordinates k p).1 ∧
      0 ≤ (signedSectorCoordinates k p).2 ∧
      (signedSectorCoordinates k p).2 ≤ (signedSectorCoordinates k p).1 := by
  obtain ⟨k, hk⟩ := exists_signedSector p
  exact ⟨k, hk.first_pos k p hp, hk⟩

theorem primitive_exists_signedSectorCoordinates (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    ∃ k : Fin 8, 0 < (signedSectorCoordinates k p).1 ∧
      0 ≤ (signedSectorCoordinates k p).2 ∧
      (signedSectorCoordinates k p).2 ≤ (signedSectorCoordinates k p).1 ∧
      IsCoprime (signedSectorCoordinates k p).1 (signedSectorCoordinates k p).2 := by
  have hp0 : p ≠ (0, 0) := by
    intro h
    subst p
    obtain ⟨a, b, h⟩ := hp
    norm_num at h
  obtain ⟨k, hk1, hk2, hk3⟩ := exists_positive_signedSectorCoordinates p hp0
  exact ⟨k, hk1, hk2, hk3, signedSectorCoordinates_coprime k p hp⟩

/-- The same actual coordinate transformation on the standard Euclidean plane. -/
def signedEuclideanCoordinates (k : Fin 8)
    (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  let p := signedPairCoordinates k (x 0, x 1)
  WithLp.toLp 2 ![p.1, p.2]

@[simp] theorem signedEuclideanCoordinates_inverse (k : Fin 8)
    (x : EuclideanSpace ℝ (Fin 2)) :
    signedEuclideanCoordinates (signedSectorInverse k) (signedEuclideanCoordinates k x) = x := by
  fin_cases k <;> ext i <;> fin_cases i <;>
    simp [signedEuclideanCoordinates, signedPairCoordinates, signedSectorInverse]

theorem signedEuclideanCoordinates_add (k : Fin 8)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    signedEuclideanCoordinates k (x + y) =
      signedEuclideanCoordinates k x + signedEuclideanCoordinates k y := by
  fin_cases k <;> ext i <;> fin_cases i <;>
    simp [signedEuclideanCoordinates, signedPairCoordinates, add_comm]

theorem signedEuclideanCoordinates_smul (k : Fin 8) (a : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    signedEuclideanCoordinates k (a • x) = a • signedEuclideanCoordinates k x := by
  fin_cases k <;> ext i <;> fin_cases i <;>
    simp [signedEuclideanCoordinates, signedPairCoordinates]

@[simp] theorem signedEuclideanCoordinates_norm (k : Fin 8)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖signedEuclideanCoordinates k x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  fin_cases k <;> simp [signedEuclideanCoordinates, signedPairCoordinates, Fin.sum_univ_two,
    add_comm]

/-- A signed coordinate permutation, bundled with its linear inverse and
preservation of the actual Euclidean norm. -/
def signedEuclideanEquiv (k : Fin 8) :
    EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun := signedEuclideanCoordinates k
  invFun := signedEuclideanCoordinates (signedSectorInverse k)
  left_inv := signedEuclideanCoordinates_inverse k
  right_inv := by
    intro x
    simpa only [signedSectorInverse_involutive] using
      signedEuclideanCoordinates_inverse (signedSectorInverse k) x
  map_add' := signedEuclideanCoordinates_add k
  map_smul' := signedEuclideanCoordinates_smul k
  norm_map' := signedEuclideanCoordinates_norm k

/-- The integer embedding uses Euclidean, rather than maximum, norm. -/
def sectorEuclideanEmbedding (p : ℤ × ℤ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(p.1 : ℝ), (p.2 : ℝ)]

@[simp] theorem sectorEuclideanEmbedding_norm (p : ℤ × ℤ) :
    ‖sectorEuclideanEmbedding p‖ = intEuclidean p := by
  simp [EuclideanSpace.norm_eq, sectorEuclideanEmbedding, Fin.sum_univ_two,
    intEuclidean, Real.norm_eq_abs, sq_abs]

/-- Real and integer signed coordinate maps agree exactly on embedded vectors. -/
@[simp] theorem signedEuclideanCoordinates_embedding (k : Fin 8) (p : ℤ × ℤ) :
    signedEuclideanCoordinates k (sectorEuclideanEmbedding p) =
      sectorEuclideanEmbedding (signedSectorCoordinates k p) := by
  fin_cases k <;> ext i <;> fin_cases i <;>
    simp [signedEuclideanCoordinates, signedPairCoordinates, sectorEuclideanEmbedding,
      signedSectorCoordinates]

def euclideanCoordinateDet (u v : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  u 0 * v 1 - u 1 * v 0

theorem signedEuclideanCoordinates_abs_det (k : Fin 8)
    (u v : EuclideanSpace ℝ (Fin 2)) :
    |euclideanCoordinateDet (signedEuclideanCoordinates k u) (signedEuclideanCoordinates k v)| =
      |euclideanCoordinateDet u v| := by
  have habs (a b : ℝ) : |-a + b| = |a - b| := by
    rw [show -a + b = -(a - b) by ring, abs_neg]
  fin_cases k <;>
    simp [signedEuclideanCoordinates, signedPairCoordinates, euclideanCoordinateDet,
      abs_sub_comm] <;> ring_nf
  all_goals exact habs _ _

/-- Two directions in the same closed sector have canonical coordinates
under one common map, with the full absolute determinant unchanged. -/
theorem signedSector_pair_reduction (k : Fin 8) (u v : ℤ × ℤ)
    (hu : InSignedSector k u) (hv : InSignedSector k v)
    (hu0 : u ≠ (0, 0)) (hv0 : v ≠ (0, 0)) :
    0 < (signedSectorCoordinates k u).1 ∧
    0 ≤ (signedSectorCoordinates k u).2 ∧
    (signedSectorCoordinates k u).2 ≤ (signedSectorCoordinates k u).1 ∧
    0 < (signedSectorCoordinates k v).1 ∧
    0 ≤ (signedSectorCoordinates k v).2 ∧
    (signedSectorCoordinates k v).2 ≤ (signedSectorCoordinates k v).1 ∧
    |intDet (signedSectorCoordinates k u) (signedSectorCoordinates k v)| = |intDet u v| :=
  ⟨hu.first_pos k u hu0, hu.1, hu.2, hv.first_pos k v hv0, hv.1, hv.2,
    signedSectorCoordinates_abs_det k u v⟩

/-- Euclidean coordinates associated to any real basis. This construction
uses no norm on the source vector space. -/
def sectorBasisEuclideanEquiv {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : Module.Basis (Fin 2) ℝ E) : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  B.equivFun.trans (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm

@[simp] theorem sectorBasisEuclideanEquiv_intVector {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (B : Module.Basis (Fin 2) ℝ E) (p : ℤ × ℤ) :
    sectorBasisEuclideanEquiv B (intVector B p) = sectorEuclideanEmbedding p := by
  ext i
  fin_cases i <;> simp [sectorBasisEuclideanEquiv, sectorEuclideanEmbedding, intVector]

/-- The original basis transported by the inverse signed coordinate map.
In a normed source, this changes the basis and leaves its norm in place. -/
def signedSectorBasis {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : Module.Basis (Fin 2) ℝ E) (k : Fin 8) : Module.Basis (Fin 2) ℝ E :=
  B.map ((sectorBasisEuclideanEquiv B).trans
    ((signedEuclideanEquiv (signedSectorInverse k)).toLinearEquiv.trans
      (sectorBasisEuclideanEquiv B).symm))

/-- Transforming an integer direction and the basis in opposite directions
represents exactly the original vector, rather than a reflected norm value. -/
theorem signedSectorBasis_intVector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Module.Basis (Fin 2) ℝ E) (k : Fin 8) (p : ℤ × ℤ) :
    intVector (signedSectorBasis B k) (signedSectorCoordinates k p) = intVector B p := by
  have hmap (q : ℤ × ℤ) :
      intVector (signedSectorBasis B k) q =
        (sectorBasisEuclideanEquiv B).symm
          (signedEuclideanCoordinates (signedSectorInverse k)
            (sectorBasisEuclideanEquiv B (intVector B q))) := by
    simp [signedSectorBasis, intVector, signedEuclideanEquiv, map_add, map_smul,
      signedEuclideanCoordinates_add, signedEuclideanCoordinates_smul]
  rw [hmap, sectorBasisEuclideanEquiv_intVector,
    ← signedEuclideanCoordinates_embedding, signedEuclideanCoordinates_inverse,
    ← sectorBasisEuclideanEquiv_intVector B p]
  exact (sectorBasisEuclideanEquiv B).symm_apply_apply _

end Markov
