import Markov.Basic
import Mathlib.Data.Set.Card

/-! Exact subtraction of the two actual small ordered Markov triples.
The count remains the original `triplesUpTo`, without a uniqueness conjecture. -/
noncomputable section
open Classical
namespace Markov

def t1_markovExceptionalFinset : Finset (ℕ × ℕ × ℕ) := {(1,1,1),(1,1,2)}

def t1_nonexceptionalTriplesUpTo (x : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {t | (IsOrderedTriple t.1 t.2.1 t.2.2 ∧ t ≠ (1,1,1) ∧ t ≠ (1,1,2)) ∧
    (t.2.2 : ℝ) ≤ x}

theorem t1_markovExceptionalFinset_card : t1_markovExceptionalFinset.card = 2 := by decide

theorem t1_markovExceptionalFinset_subset (x : ℝ) (hx : 2 ≤ x) :
    t1_markovExceptionalFinset ⊆ triplesUpTo ⌊x⌋₊ := by
  intro t ht
  simp only [t1_markovExceptionalFinset,Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl
  · rw [mem_triplesUpTo_floor x (by linarith)]
    exact ⟨by decide,by norm_num; linarith⟩
  · rw [mem_triplesUpTo_floor x (by linarith)]
    exact ⟨by decide,hx⟩

theorem t1_nonexceptionalTriplesUpTo_eq_sdiff (x : ℝ) (hx : 0 ≤ x) :
    t1_nonexceptionalTriplesUpTo x =
      ↑(triplesUpTo ⌊x⌋₊ \ t1_markovExceptionalFinset) := by
  ext t
  rcases t with ⟨p,q,r⟩
  simp only [t1_nonexceptionalTriplesUpTo,Set.mem_setOf_eq,Finset.mem_coe,
    Finset.mem_sdiff,t1_markovExceptionalFinset,Finset.mem_insert,Finset.mem_singleton]
  rw [mem_triplesUpTo_floor x hx]
  tauto

theorem t1_nonexceptionalTriplesUpTo_count (x : ℝ) (hx : 2 ≤ x) :
    (t1_nonexceptionalTriplesUpTo x).ncard + 2 = countNat ⌊x⌋₊ := by
  rw [t1_nonexceptionalTriplesUpTo_eq_sdiff x (by linarith)]
  have hcard := Finset.card_sdiff_add_card_eq_card (t1_markovExceptionalFinset_subset x hx)
  simpa only [Set.ncard_coe_finset,t1_markovExceptionalFinset_card,countNat] using hcard

theorem t1_nonexceptionalTriplesUpTo_real_count (x : ℝ) (hx : 2 ≤ x) :
    ((t1_nonexceptionalTriplesUpTo x).ncard : ℝ) + 2 = count x := by
  unfold count
  exact_mod_cast t1_nonexceptionalTriplesUpTo_count x hx

end Markov
