import Markov.Basic

/-! Actual Vieta reflection and strict descent for sorted Markov triples.
No uniqueness of a triple from its largest coordinate is assumed. -/

namespace Markov

theorem t1_ordered_markov_largest_lt (p q r : ℕ) (h : IsOrderedTriple p q r) :
    r < 3 * p * q := by
  obtain ⟨hp, hpq, hqr, heq⟩ := h
  by_contra! hbad
  have hmul := Nat.mul_le_mul_right r hbad
  nlinarith [sq_pos_of_pos hp]

/-- The reflected coordinate has its literal complementary-root product. -/
theorem t1_vieta_complement_product (p q r : ℕ) (h : IsOrderedTriple p q r) :
    (3 * p * q - r) * r = p ^ 2 + q ^ 2 := by
  have hsum := Nat.sub_add_cancel (Nat.le_of_lt (t1_ordered_markov_largest_lt p q r h))
  obtain ⟨_, _, _, heq⟩ := h
  nlinarith

theorem t1_vieta_complement_pos (p q r : ℕ) (h : IsOrderedTriple p q r) :
    0 < 3 * p * q - r :=
  Nat.sub_pos_of_lt (t1_ordered_markov_largest_lt p q r h)

/-- Vieta reflection preserves the actual Diophantine equation. -/
theorem t1_vieta_complement_equation (p q r : ℕ) (h : IsOrderedTriple p q r) :
    p ^ 2 + q ^ 2 + (3 * p * q - r) ^ 2 = 3 * p * q * (3 * p * q - r) := by
  have hsum := Nat.sub_add_cancel (Nat.le_of_lt (t1_ordered_markov_largest_lt p q r h))
  have hprod := t1_vieta_complement_product p q r h
  nlinarith

/-- Away from the two `(1,1,*)` exceptional triples the reflected coordinate
is strictly below the former middle coordinate. -/
theorem t1_vieta_strict_descent (p q r : ℕ) (h : IsOrderedTriple p q r)
    (hex : p ≠ 1 ∨ q ≠ 1) :
    3 * p * q - r < q := by
  obtain ⟨hp, hpq, hqr, heq⟩ := h
  have hfull : IsOrderedTriple p q r := ⟨hp, hpq, hqr, heq⟩
  have hsum := Nat.sub_add_cancel (Nat.le_of_lt (t1_ordered_markov_largest_lt p q r hfull))
  have hprod := t1_vieta_complement_product p q r hfull
  by_contra! hbad
  have hfac : 0 ≤ (r - q : ℕ) * (3 * p * q - r - q) := Nat.zero_le _
  have hrq : r = (r - q) + q := (Nat.sub_add_cancel hqr).symm
  have hvq : 3 * p * q - r = (3 * p * q - r - q) + q :=
    (Nat.sub_add_cancel hbad).symm
  have hpoly : 3 * p * q * q ≤ p ^ 2 + 2 * q ^ 2 := by
    nlinarith
  by_cases hpone : p = 1
  · have hq : 2 ≤ q := by omega
    subst p
    nlinarith
  · have hp2 : 2 ≤ p := by omega
    have hqpos : 0 < q := lt_of_lt_of_le hp hpq
    have hpq2 : p ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hpq 2
    have hmul : 6 * q ^ 2 ≤ (3 * p) * q ^ 2 :=
      Nat.mul_le_mul_right (q ^ 2) (by omega)
    nlinarith [sq_pos_of_pos hqpos]

theorem t1_markov_exceptional (r : ℕ) (h : IsOrderedTriple 1 1 r) :
    r = 1 ∨ r = 2 := by
  obtain ⟨_, _, hr, heq⟩ := h
  have hr2 : r ≤ 2 := by nlinarith
  omega

/-- The explicit sorted parent is an actual smaller Markov triple. -/
theorem t1_markov_sorted_parent (p q r : ℕ) (h : IsOrderedTriple p q r)
    (hex : p ≠ 1 ∨ q ≠ 1) :
    IsOrderedTriple (min p (3*p*q-r)) (max p (3*p*q-r)) q ∧ q < r := by
  have hp := h.1
  have hpq := h.2.1
  have hqr := h.2.2.1
  have hvpos := t1_vieta_complement_pos p q r h
  have hvlt := t1_vieta_strict_descent p q r h hex
  have hveq := t1_vieta_complement_equation p q r h
  have hprod := t1_vieta_complement_product p q r h
  have hqpos : 0 < q := lt_of_lt_of_le hp hpq
  have hstrict : q < r := by
    by_contra! hbad
    have hrq : r = q := Nat.le_antisymm hbad hqr
    rw [hrq] at hprod
    have hmul := Nat.mul_lt_mul_of_pos_right hvlt hqpos
    rw [hrq] at hmul
    nlinarith [sq_pos_of_pos hp]
  refine ⟨?_, hstrict⟩
  by_cases horder : p ≤ 3*p*q-r
  · simp only [min_eq_left horder, max_eq_right horder]
    exact ⟨hp, horder, hvlt.le, by nlinarith⟩
  · have horder' : 3*p*q-r ≤ p := Nat.le_of_lt (Nat.lt_of_not_ge horder)
    simp only [min_eq_right horder', max_eq_left horder']
    exact ⟨hvpos, horder', hpq, by nlinarith⟩

end Markov
