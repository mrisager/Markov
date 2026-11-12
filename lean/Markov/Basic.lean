import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-! The paper's ordered Markov triples and their actual counting function. -/

namespace Markov

/-- Positive Markov triples in nondecreasing order. -/
def IsOrderedTriple (p q r : ℕ) : Prop :=
  0 < p ∧ p ≤ q ∧ q ≤ r ∧ p ^ 2 + q ^ 2 + r ^ 2 = 3 * p * q * r

instance (p q r : ℕ) : Decidable (IsOrderedTriple p q r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Counts triples, so this does not assume Frobenius uniqueness. -/
def triplesUpTo (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)).product
    ((Finset.range (n + 1)).product (Finset.range (n + 1)))).filter
      (fun t => IsOrderedTriple t.1 t.2.1 t.2.2)

theorem mem_triplesUpTo (n p q r : ℕ) :
    (p, q, r) ∈ triplesUpTo n ↔ IsOrderedTriple p q r ∧ r ≤ n := by
  simp only [triplesUpTo, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, _, hr⟩, ht⟩
    exact ⟨ht, by omega⟩
  · rintro ⟨ht, hr⟩
    obtain ⟨hp, hpq, hqr, heq⟩ := ht
    exact ⟨⟨by omega, by omega, by omega⟩, hp, hpq, hqr, heq⟩

def countNat (n : ℕ) : ℕ := (triplesUpTo n).card

/-- The real-valued counting function `M(x)` in the paper. -/
noncomputable def count (x : ℝ) : ℝ := (countNat ⌊x⌋₊ : ℝ)

theorem mem_triplesUpTo_floor (x : ℝ) (hx : 0 ≤ x) (p q r : ℕ) :
    (p, q, r) ∈ triplesUpTo ⌊x⌋₊ ↔ IsOrderedTriple p q r ∧ (r : ℝ) ≤ x := by
  rw [mem_triplesUpTo, Nat.le_floor_iff hx]

theorem triplesUpTo_mono {m n : ℕ} (h : m ≤ n) : triplesUpTo m ⊆ triplesUpTo n := by
  intro t ht
  rcases t with ⟨p, q, r⟩
  rw [mem_triplesUpTo] at ht ⊢
  exact ⟨ht.1, ht.2.trans h⟩

theorem countNat_mono : Monotone countNat := by
  intro m n h
  exact Finset.card_le_card (triplesUpTo_mono h)

/-- Kernel-reduced check at the two exceptional triples. -/
theorem countNat_two : countNat 2 = 2 := by decide

end Markov
