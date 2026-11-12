import T1MarkovGeneration

/-! Soundness and genuine height increase of the two sorted Vieta children.
This does not identify triples by their largest coordinate. -/
namespace Markov

theorem t1_ordered_markov_left_child (p q r : ℕ) (h : IsOrderedTriple p q r) :
    IsOrderedTriple p r (3*p*r-q) ∧ r < 3*p*r-q := by
  obtain ⟨hp, hpq, hqr, heq⟩ := h
  have hr : 0 < r := hp.trans_le (hpq.trans hqr)
  have hpr : r ≤ p*r := by nlinarith
  have hq : q ≤ 3*p*r := by nlinarith
  have hsum := Nat.sub_add_cancel hq
  have hinc : r < 3*p*r-q := by nlinarith
  have heqZ : (p : ℤ)^2 + (q : ℤ)^2 + (r : ℤ)^2 = 3*p*q*r := by exact_mod_cast heq
  have hnew : p^2+r^2+(3*p*r-q)^2=3*p*r*(3*p*r-q) := by
    zify [hq]
    nlinarith only [heqZ]
  exact ⟨⟨hp, hpq.trans hqr, hinc.le, hnew⟩, hinc⟩

theorem t1_ordered_markov_right_child (p q r : ℕ) (h : IsOrderedTriple p q r) :
    IsOrderedTriple q r (3*q*r-p) ∧ r < 3*q*r-p := by
  obtain ⟨hp, hpq, hqr, heq⟩ := h
  have hqpos := hp.trans_le hpq
  have hr := hqpos.trans_le hqr
  have hqrprod : r ≤ q*r := by nlinarith
  have hp' : p ≤ 3*q*r := by nlinarith
  have hsum := Nat.sub_add_cancel hp'
  have hinc : r < 3*q*r-p := by nlinarith
  have heqZ : (p : ℤ)^2 + (q : ℤ)^2 + (r : ℤ)^2 = 3*p*q*r := by exact_mod_cast heq
  have hnew : q^2+r^2+(3*q*r-p)^2=3*q*r*(3*q*r-p) := by
    zify [hp']
    nlinarith only [heqZ]
  exact ⟨⟨hqpos, hqr, hinc.le, hnew⟩, hinc⟩

theorem t1_vietaSuccessor_preserves_ordered {s t : ℕ × ℕ × ℕ}
    (hs : IsOrderedTriple s.1 s.2.1 s.2.2) (hstep : t1_vietaSuccessor s t) :
    IsOrderedTriple t.1 t.2.1 t.2.2 := by
  rcases s with ⟨p,q,r⟩
  rcases hstep with rfl | rfl
  · exact (t1_ordered_markov_left_child p q r hs).1
  · exact (t1_ordered_markov_right_child p q r hs).1

theorem t1_markovGenerated_ordered {t : ℕ × ℕ × ℕ} (h : t1_markovGenerated t) :
    IsOrderedTriple t.1 t.2.1 t.2.2 := by
  induction h with
  | refl => decide
  | tail _ hstep ih => exact t1_vietaSuccessor_preserves_ordered ih hstep

theorem t1_markovGenerated_iff_ordered (p q r : ℕ) :
    t1_markovGenerated (p,q,r) ↔ IsOrderedTriple p q r :=
  ⟨t1_markovGenerated_ordered, t1_all_ordered_markov_generated r p q⟩

end Markov
