import Markov.PrimitivePartner
import Markov.QuadrantSeeds
import Markov.SeededFarey

/-! Coverage of primitive integral directions by the four concrete seeded
Farey constructions. Rotations here are integer coordinate changes only;
no symmetry of a norm or surface is assumed. -/

namespace Markov

/-- Coordinates in the counterclockwise quadrant basis. These are inverse
quarter-turns of the actual direction vector. -/
def quadrantCoordinates : Fin 4 → (ℤ × ℤ) → (ℤ × ℤ)
  | 0, p => p
  | 1, p => (p.2, -p.1)
  | 2, p => (-p.1, -p.2)
  | 3, p => (-p.2, p.1)

/-- Coordinates in a quadrant basis reconstruct the original integer vector. -/
theorem quadrantCoordinates_reconstruct (k : Fin 4) (p : ℤ × ℤ) :
    seededDirection (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantCoordinates k p) = p := by
  fin_cases k <;> ext <;>
    simp [quadrantCoordinates, quadrantSeedDirections, seededDirection]

/-- The coordinate rotations preserve oriented integer determinants. -/
theorem quadrantCoordinates_det (k : Fin 4) (u v : ℤ × ℤ) :
    intDet (quadrantCoordinates k u) (quadrantCoordinates k v) = intDet u v := by
  fin_cases k <;> simp [quadrantCoordinates, intDet] <;> ring

/-- Integer primitivity is preserved by quadrant coordinate changes. -/
theorem quadrantCoordinates_coprime (k : Fin 4) (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    IsCoprime (quadrantCoordinates k p).1 (quadrantCoordinates k p).2 := by
  fin_cases k
  · exact hp
  · exact hp.symm.neg_right
  · exact hp.neg_neg
  · exact hp.symm.neg_left

/-- Every integer direction has nonnegative coordinates in at least one of
the four actual quadrant bases, including their boundary rays. -/
theorem exists_nonnegative_quadrantCoordinates (p : ℤ × ℤ) :
    ∃ k : Fin 4, 0 ≤ (quadrantCoordinates k p).1 ∧ 0 ≤ (quadrantCoordinates k p).2 := by
  by_cases hx : 0 ≤ p.1
  · by_cases hy : 0 ≤ p.2
    · exact ⟨0, hx, hy⟩
    · refine ⟨3, ?_, hx⟩
      dsimp [quadrantCoordinates]
      omega
  · by_cases hy : 0 ≤ p.2
    · refine ⟨1, hy, ?_⟩
      dsimp [quadrantCoordinates]
      omega
    · refine ⟨2, ?_, ?_⟩ <;> dsimp [quadrantCoordinates] <;> omega

/-- A determinant-one pair contained in one quadrant has actual matrix words
in the corresponding concrete seeded construction. -/
theorem exists_quadrantSeededFarey_of_coordinates (k : Fin 4) (u v : ℤ × ℤ)
    (hu1 : 0 ≤ (quadrantCoordinates k u).1) (hu2 : 0 ≤ (quadrantCoordinates k u).2)
    (hv1 : 0 ≤ (quadrantCoordinates k v).1) (hv2 : 0 ≤ (quadrantCoordinates k v).2)
    (hd : intDet u v = 1) :
    ∃ M N, SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N := by
  have hc : intDet (quadrantCoordinates k u) (quadrantCoordinates k v) = 1 := by
    rw [quadrantCoordinates_det, hd]
  obtain ⟨M, N, h⟩ := exists_seededFarey_of_nonnegative_coordinates
    (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
    (quadrantCoordinates k u) (quadrantCoordinates k v)
    (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 hu1 hu2 hv1 hv2 hc
  exact ⟨M, N, by simpa only [quadrantCoordinates_reconstruct] using h⟩

/-- Every primitive integral vector occurs as a label of actual integer
matrix words in one of the four concrete quadrant constructions. -/
theorem primitive_exists_quadrantSeededFarey (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    ∃ (k : Fin 4) (u v : ℤ × ℤ) (M N : IntMatrixTwo),
      SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
        (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N ∧
      (p = u ∨ p = v) := by
  obtain ⟨k, hk1, hk2⟩ := exists_nonnegative_quadrantCoordinates p
  have hcop := quadrantCoordinates_coprime k p hp
  obtain ⟨a, b, ha1, ha2, hb1, hb2, hd, hpab⟩ :=
    nonnegative_primitive_in_unimodular_pair (quadrantCoordinates k p) hk1 hk2 hcop
  obtain ⟨M, N, h⟩ := exists_seededFarey_of_nonnegative_coordinates
    (quadrantSeedDirections k).1 (quadrantSeedDirections k).2 a b
    (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 ha1 ha2 hb1 hb2 hd
  refine ⟨k, seededDirection (quadrantSeedDirections k).1 (quadrantSeedDirections k).2 a,
    seededDirection (quadrantSeedDirections k).1 (quadrantSeedDirections k).2 b,
    M, N, h, ?_⟩
  have hrec := quadrantCoordinates_reconstruct k p
  rcases hpab with hpa | hpb
  · left
    rw [hpa] at hrec
    exact hrec.symm
  · right
    rw [hpb] at hrec
    exact hrec.symm

/-- The integer quarter-turns preserve infinity height. This is a statement
about coordinates, not a symmetry assertion about any geometric norm. -/
theorem quadrantCoordinates_height (k : Fin 4) (p : ℤ × ℤ) :
    intHeight (quadrantCoordinates k p) = intHeight p := by
  fin_cases k <;> simp [quadrantCoordinates, intHeight, max_comm]

theorem quadrantSeededDirection_height (k : Fin 4) (p : ℤ × ℤ) :
    intHeight (seededDirection (quadrantSeedDirections k).1 (quadrantSeedDirections k).2 p) =
      intHeight p := by
  fin_cases k <;> simp [quadrantSeedDirections, seededDirection, intHeight, max_comm]

/-- A primitive direction can be placed in a quadrant with strictly positive
first coordinate. Boundary directions use the quadrant beginning at that ray. -/
theorem primitive_exists_positive_first_quadrantCoordinates (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    ∃ k : Fin 4, 0 < (quadrantCoordinates k p).1 ∧ 0 ≤ (quadrantCoordinates k p).2 := by
  by_cases hx0 : p.1 = 0
  · have hy0 : p.2 ≠ 0 := by
      intro hy0
      obtain ⟨s, t, h⟩ := hp
      simp [hx0, hy0] at h
    by_cases hy : 0 < p.2
    · refine ⟨1, hy, ?_⟩
      simp [quadrantCoordinates, hx0]
    · refine ⟨3, ?_, ?_⟩ <;> dsimp [quadrantCoordinates] <;> omega
  · by_cases hx : 0 < p.1
    · by_cases hy : 0 ≤ p.2
      · exact ⟨0, hx, hy⟩
      · refine ⟨3, ?_, hx.le⟩
        dsimp [quadrantCoordinates]
        omega
    · by_cases hy : 0 < p.2
      · refine ⟨1, hy, ?_⟩
        dsimp [quadrantCoordinates]
        omega
      · refine ⟨2, ?_, ?_⟩ <;> dsimp [quadrantCoordinates] <;> omega

/-- A nonnegative primitive direction with positive first coordinate has a
right unimodular partner of no greater infinity height. -/
theorem positive_first_primitive_right_partner (p : ℤ × ℤ)
    (ha : 0 < p.1) (hb : 0 ≤ p.2) (hp : IsCoprime p.1 p.2) :
    ∃ q : ℤ × ℤ, 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ intDet p q = 1 ∧ intHeight q ≤ intHeight p := by
  by_cases hb0 : p.2 = 0
  · have hpseed : p = (1, 0) := by
      rcases nonnegative_primitive_axis p ha.le hb hp (Or.inr hb0) with hh | hh
      · exact hh
      · have hz := congrArg Prod.fst hh
        omega
    subst p
    exact ⟨(0, 1), by norm_num [intDet, intHeight]⟩
  · have hbpos : 0 < p.2 := by omega
    obtain ⟨c, d, hc, hca, hd, hdb, hdet⟩ :=
      positive_coprime_bounded_partner p.1 p.2 ha hbpos hp
    refine ⟨(c, d), hc, by omega, hdet, ?_⟩
    change max |(c : ℝ)| |(d : ℝ)| ≤ max |(p.1 : ℝ)| |(p.2 : ℝ)|
    apply max_le_max
    · rw [abs_of_nonneg (by exact_mod_cast hc), abs_of_nonneg (by exact_mod_cast ha.le)]
      exact_mod_cast hca.le
    · rw [abs_of_nonneg (by exact_mod_cast (show 0 ≤ d by omega)),
        abs_of_nonneg (by exact_mod_cast hb)]
      exact_mod_cast hdb

/-- Every primitive integral direction occurs specifically as the left
label of a concrete quadrant Farey pair whose right label has no greater
infinity height. All matrices are constructed from the actual quadrant seeds. -/
theorem primitive_exists_quadrantSeededFarey_left (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    ∃ (k : Fin 4) (q : ℤ × ℤ) (M N : IntMatrixTwo),
      SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
        (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 p q M N ∧
      intHeight q ≤ intHeight p := by
  obtain ⟨k, hk1, hk2⟩ := primitive_exists_positive_first_quadrantCoordinates p hp
  obtain ⟨r, hr1, hr2, hd, hheight⟩ := positive_first_primitive_right_partner
    (quadrantCoordinates k p) hk1 hk2 (quadrantCoordinates_coprime k p hp)
  obtain ⟨M, N, hh⟩ := exists_seededFarey_of_nonnegative_coordinates
    (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
    (quadrantCoordinates k p) r (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
    hk1.le hk2 hr1 hr2 hd
  refine ⟨k, seededDirection (quadrantSeedDirections k).1 (quadrantSeedDirections k).2 r,
    M, N, ?_, ?_⟩
  · simpa only [quadrantCoordinates_reconstruct] using hh
  · rw [quadrantSeededDirection_height]
    exact hheight.trans_eq (quadrantCoordinates_height k p)

/-- The dual quadrant choice places a primitive vector with strictly
positive second coordinate. -/
theorem primitive_exists_positive_second_quadrantCoordinates (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    ∃ k : Fin 4, 0 ≤ (quadrantCoordinates k p).1 ∧ 0 < (quadrantCoordinates k p).2 := by
  obtain ⟨k, hk1, hk2⟩ := primitive_exists_positive_first_quadrantCoordinates (p.2, p.1) hp.symm
  fin_cases k
  · exact ⟨0, hk2, hk1⟩
  · exact ⟨3, hk2, hk1⟩
  · exact ⟨2, hk2, hk1⟩
  · exact ⟨1, hk2, hk1⟩

/-- A nonnegative primitive direction with positive second coordinate has a
left unimodular partner of no greater infinity height. -/
theorem positive_second_primitive_left_partner (p : ℤ × ℤ)
    (ha : 0 ≤ p.1) (hb : 0 < p.2) (hp : IsCoprime p.1 p.2) :
    ∃ q : ℤ × ℤ, 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ intDet q p = 1 ∧ intHeight q ≤ intHeight p := by
  obtain ⟨r, hr1, hr2, hd, hh⟩ := positive_first_primitive_right_partner (p.2, p.1) hb ha hp.symm
  refine ⟨(r.2, r.1), hr2, hr1, ?_, ?_⟩
  · dsimp [intDet] at *
    nlinarith
  · simpa only [intHeight, max_comm] using hh

/-- Every primitive integral direction also occurs specifically as the
right label, with a left label of no greater infinity height. -/
theorem primitive_exists_quadrantSeededFarey_right (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    ∃ (k : Fin 4) (q : ℤ × ℤ) (M N : IntMatrixTwo),
      SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
        (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 q p M N ∧
      intHeight q ≤ intHeight p := by
  obtain ⟨k, hk1, hk2⟩ := primitive_exists_positive_second_quadrantCoordinates p hp
  obtain ⟨r, hr1, hr2, hd, hheight⟩ := positive_second_primitive_left_partner
    (quadrantCoordinates k p) hk1 hk2 (quadrantCoordinates_coprime k p hp)
  obtain ⟨M, N, hh⟩ := exists_seededFarey_of_nonnegative_coordinates
    (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
    r (quadrantCoordinates k p) (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
    hr1 hr2 hk1 hk2.le hd
  refine ⟨k, seededDirection (quadrantSeedDirections k).1 (quadrantSeedDirections k).2 r,
    M, N, ?_, ?_⟩
  · simpa only [quadrantCoordinates_reconstruct] using hh
  · rw [quadrantSeededDirection_height]
    exact hheight.trans_eq (quadrantCoordinates_height k p)

end Markov
