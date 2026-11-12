import Markov.QuadrantCoverage

/-! Every primitive direction is either one of the four quadrant axes or
is born as the sum of the labels of an actual quadrant Farey pair. -/

namespace Markov

/-- Each label is an original seed label or the sum of an earlier actual pair. -/
theorem SeededFarey.labels_seed_or_birth
    {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey u0 v0 M0 N0 u v M N) :
    (u = u0 ∨ u = v0 ∨ ∃ a b P Q,
      SeededFarey u0 v0 M0 N0 a b P Q ∧ u = a + b) ∧
    (v = u0 ∨ v = v0 ∨ ∃ a b P Q,
      SeededFarey u0 v0 M0 N0 a b P Q ∧ v = a + b) := by
  induction h with
  | seed => exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
  | @left a b P Q h ih =>
    exact ⟨ih.1, Or.inr (Or.inr ⟨a, b, P, Q, h, rfl⟩)⟩
  | @right a b P Q h ih =>
    exact ⟨Or.inr (Or.inr ⟨a, b, P, Q, h, rfl⟩), ih.2⟩

/-- The second axis of one quadrant is the first axis of another. -/
theorem quadrantSeed_snd_eq_fst (k : Fin 4) :
    ∃ j : Fin 4, (quadrantSeedDirections k).2 = (quadrantSeedDirections j).1 := by
  fin_cases k
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨0, rfl⟩

/-- Every primitive integer direction is a quadrant axis or the sum label
of an actual quadrant Farey pair. -/
theorem primitive_quadrant_seed_or_birth (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    (∃ k : Fin 4, p = (quadrantSeedDirections k).1) ∨
    ∃ (k : Fin 4) (u v : ℤ × ℤ) (M N : IntMatrixTwo),
      SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
        (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N ∧ p = u + v := by
  obtain ⟨k, u, v, M, N, h, hpv⟩ := primitive_exists_quadrantSeededFarey p hp
  have hlabel : p = (quadrantSeedDirections k).1 ∨
      p = (quadrantSeedDirections k).2 ∨
      ∃ a b P Q, SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
        (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 a b P Q ∧ p = a + b := by
    rcases hpv with rfl | rfl
    · exact h.labels_seed_or_birth.1
    · exact h.labels_seed_or_birth.2
  rcases hlabel with haxis | haxis | ⟨a, b, P, Q, hab, hpab⟩
  · exact Or.inl ⟨k, haxis⟩
  · obtain ⟨j, hj⟩ := quadrantSeed_snd_eq_fst k
    exact Or.inl ⟨j, haxis.trans hj⟩
  · exact Or.inr ⟨k, a, b, P, Q, hab, hpab⟩

end Markov
