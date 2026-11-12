import Markov.SignedSectors

/-! Actual quadrant matrix words for pairs recovered from any of the eight
canonical signed sectors. Reflected sectors reverse the endpoint order; all
directions and heights remain those of the original lattice. -/

namespace Markov

def inverseSignedSectorCoordinates (k : Fin 8) (p : ℤ × ℤ) : ℤ × ℤ :=
  signedSectorCoordinates (signedSectorInverse k) p

@[simp] theorem inverseSignedSectorCoordinates_coordinates (k : Fin 8) (p : ℤ × ℤ) :
    inverseSignedSectorCoordinates k (signedSectorCoordinates k p) = p :=
  signedSectorCoordinates_inverse k p

@[simp] theorem coordinates_inverseSignedSectorCoordinates (k : Fin 8) (p : ℤ × ℤ) :
    signedSectorCoordinates k (inverseSignedSectorCoordinates k p) = p := by
  simpa only [inverseSignedSectorCoordinates, signedSectorInverse_involutive] using
    signedSectorCoordinates_inverse (signedSectorInverse k) p

@[simp] theorem inverseSignedSectorCoordinates_add (k : Fin 8) (u v : ℤ × ℤ) :
    inverseSignedSectorCoordinates k (u + v) =
      inverseSignedSectorCoordinates k u + inverseSignedSectorCoordinates k v :=
  signedSectorCoordinates_add (signedSectorInverse k) u v

@[simp] theorem inverseSignedSectorCoordinates_height (k : Fin 8) (p : ℤ × ℤ) :
    intHeight (inverseSignedSectorCoordinates k p) = intHeight p :=
  signedSectorCoordinates_height (signedSectorInverse k) p

theorem inverseSignedSectorCoordinates_height_add (k : Fin 8) (u v : ℤ × ℤ) :
    intHeight (inverseSignedSectorCoordinates k u + inverseSignedSectorCoordinates k v) =
      intHeight (u + v) := by
  rw [← inverseSignedSectorCoordinates_add, inverseSignedSectorCoordinates_height]

@[simp] theorem inverseSignedSectorCoordinates_euclidean (k : Fin 8) (p : ℤ × ℤ) :
    intEuclidean (inverseSignedSectorCoordinates k p) = intEuclidean p :=
  signedSectorCoordinates_euclidean (signedSectorInverse k) p

/-- The common actual quadrant containing this closed signed sector. -/
def signedSectorQuadrant : Fin 8 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 0
  | 5 => 1
  | 6 => 2
  | 7 => 3

theorem quadrantCoordinates_inverseSignedSectorCoordinates (k : Fin 8) (p : ℤ × ℤ) :
    quadrantCoordinates (signedSectorQuadrant k) (inverseSignedSectorCoordinates k p) =
      if k.val < 4 then p else (p.2, p.1) := by
  fin_cases k <;> simp [signedSectorQuadrant, inverseSignedSectorCoordinates,
    signedSectorCoordinates, signedSectorInverse, signedPairCoordinates, quadrantCoordinates]

/-- The first four sectors preserve orientation, and the last four reverse it. -/
theorem inverseSignedSectorCoordinates_det (k : Fin 8) (u v : ℤ × ℤ) :
    intDet (inverseSignedSectorCoordinates k u) (inverseSignedSectorCoordinates k v) =
      if k.val < 4 then intDet u v else -intDet u v := by
  fin_cases k <;> simp [inverseSignedSectorCoordinates, signedSectorCoordinates,
    signedSectorInverse, signedPairCoordinates, intDet] <;> ring

/-- Every recovered canonical direction is nonnegative in this actual
quadrant, including directions on sector boundaries. -/
theorem inverseSignedSectorCoordinates_quadrant_nonneg (k : Fin 8) (p : ℤ × ℤ)
    (hp0 : 0 ≤ p.2) (hp1 : p.2 ≤ p.1) :
    0 ≤ (quadrantCoordinates (signedSectorQuadrant k)
      (inverseSignedSectorCoordinates k p)).1 ∧
    0 ≤ (quadrantCoordinates (signedSectorQuadrant k)
      (inverseSignedSectorCoordinates k p)).2 := by
  rw [quadrantCoordinates_inverseSignedSectorCoordinates]
  split_ifs
  · exact ⟨hp0.trans hp1, hp0⟩
  · exact ⟨hp0, hp0.trans hp1⟩

/-- A canonical determinant-one pair gives concrete matrix words in one
actual quadrant. The reflected cases use the reversed endpoint order. -/
theorem signedSector_exists_quadrantSeededFarey
    (k : Fin 8) (u v : ℤ × ℤ)
    (hu0 : 0 ≤ u.2) (hu1 : u.2 ≤ u.1)
    (hv0 : 0 ≤ v.2) (hv1 : v.2 ≤ v.1) (hd : intDet u v = 1) :
    ∃ (q : Fin 4) (M N : IntMatrixTwo),
      0 ≤ (quadrantCoordinates q (inverseSignedSectorCoordinates k u)).1 ∧
      0 ≤ (quadrantCoordinates q (inverseSignedSectorCoordinates k u)).2 ∧
      0 ≤ (quadrantCoordinates q (inverseSignedSectorCoordinates k v)).1 ∧
      0 ≤ (quadrantCoordinates q (inverseSignedSectorCoordinates k v)).2 ∧
      intHeight (inverseSignedSectorCoordinates k u) = intHeight u ∧
      intHeight (inverseSignedSectorCoordinates k v) = intHeight v ∧
      ((intDet (inverseSignedSectorCoordinates k u)
          (inverseSignedSectorCoordinates k v) = 1 ∧
        SeededFarey (quadrantSeedDirections q).1 (quadrantSeedDirections q).2
          (quadrantSeedMatrices q).1 (quadrantSeedMatrices q).2
          (inverseSignedSectorCoordinates k u) (inverseSignedSectorCoordinates k v) M N) ∨
       (intDet (inverseSignedSectorCoordinates k v)
          (inverseSignedSectorCoordinates k u) = 1 ∧
        SeededFarey (quadrantSeedDirections q).1 (quadrantSeedDirections q).2
          (quadrantSeedMatrices q).1 (quadrantSeedMatrices q).2
          (inverseSignedSectorCoordinates k v) (inverseSignedSectorCoordinates k u) M N)) := by
  obtain ⟨huq0, huq1⟩ := inverseSignedSectorCoordinates_quadrant_nonneg k u hu0 hu1
  obtain ⟨hvq0, hvq1⟩ := inverseSignedSectorCoordinates_quadrant_nonneg k v hv0 hv1
  by_cases hk : k.val < 4
  · have hd' : intDet (inverseSignedSectorCoordinates k u)
        (inverseSignedSectorCoordinates k v) = 1 := by
      rw [inverseSignedSectorCoordinates_det, if_pos hk, hd]
    obtain ⟨M, N, hword⟩ := exists_quadrantSeededFarey_of_coordinates
      (signedSectorQuadrant k) (inverseSignedSectorCoordinates k u)
      (inverseSignedSectorCoordinates k v) huq0 huq1 hvq0 hvq1 hd'
    exact ⟨signedSectorQuadrant k, M, N, huq0, huq1, hvq0, hvq1,
      inverseSignedSectorCoordinates_height k u, inverseSignedSectorCoordinates_height k v,
      Or.inl ⟨hd', hword⟩⟩
  · have hd' : intDet (inverseSignedSectorCoordinates k v)
        (inverseSignedSectorCoordinates k u) = 1 := by
      have h := inverseSignedSectorCoordinates_det k u v
      rw [if_neg hk, hd] at h
      dsimp [intDet] at h ⊢
      linarith
    obtain ⟨M, N, hword⟩ := exists_quadrantSeededFarey_of_coordinates
      (signedSectorQuadrant k) (inverseSignedSectorCoordinates k v)
      (inverseSignedSectorCoordinates k u) hvq0 hvq1 huq0 huq1 hd'
    exact ⟨signedSectorQuadrant k, M, N, huq0, huq1, hvq0, hvq1,
      inverseSignedSectorCoordinates_height k u, inverseSignedSectorCoordinates_height k v,
      Or.inr ⟨hd', hword⟩⟩

end Markov
