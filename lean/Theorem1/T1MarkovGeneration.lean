import T1MarkovDescent
import Mathlib.Logic.Relation

/-! Vieta children and generation of every ordered Markov triple by
strict descent. The count identity is in `T1ActualMarkovCountIdentity`. -/

namespace Markov

def t1_vietaLeft (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (t.1, t.2.2, 3*t.1*t.2.2-t.2.1)

def t1_vietaRight (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (t.2.1, t.2.2, 3*t.2.1*t.2.2-t.1)

def t1_vietaSuccessor (s t : ℕ × ℕ × ℕ) : Prop :=
  t = t1_vietaLeft s ∨ t = t1_vietaRight s

def t1_markovGenerated (t : ℕ × ℕ × ℕ) : Prop :=
  Relation.ReflTransGen t1_vietaSuccessor (1, 1, 1) t

/-- Every actual sorted positive Markov triple is obtained from the root
by the literal two Vieta transformations in the paper. No Frobenius
uniqueness hypothesis or largest-coordinate encoding is used. -/
theorem t1_all_ordered_markov_generated :
    ∀ r p q : ℕ, IsOrderedTriple p q r → t1_markovGenerated (p, q, r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro p q htriple
    by_cases h11 : p = 1 ∧ q = 1
    · obtain ⟨rfl, rfl⟩ := h11
      rcases t1_markov_exceptional r htriple with rfl | rfl
      · exact Relation.ReflTransGen.refl
      · apply Relation.ReflTransGen.single
        exact Or.inl rfl
    · have hex : p ≠ 1 ∨ q ≠ 1 := by omega
      have hparent := t1_markov_sorted_parent p q r htriple hex
      have hgen := ih q hparent.2 _ _ hparent.1
      have hsum := Nat.sub_add_cancel
        (Nat.le_of_lt (t1_ordered_markov_largest_lt p q r htriple))
      have hrestore : 3*p*q-(3*p*q-r) = r := by omega
      change Relation.ReflTransGen t1_vietaSuccessor (1, 1, 1) (p, q, r)
      apply Relation.ReflTransGen.tail hgen
      by_cases horder : p ≤ 3*p*q-r
      · left
        simp only [t1_vietaLeft, min_eq_left horder, max_eq_right horder]
        exact congrArg (fun n => (p, q, n)) hrestore.symm
      · right
        have horder' : 3*p*q-r ≤ p := Nat.le_of_lt (Nat.lt_of_not_ge horder)
        simp only [t1_vietaRight, min_eq_right horder', max_eq_left horder']
        exact congrArg (fun n => (p, q, n)) hrestore.symm

end Markov
