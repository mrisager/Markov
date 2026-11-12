import T1MarkovChildren

/-! The actual sorted parent is inverse to both Vieta children. The parent
is computed from all three coordinates; no largest-coordinate uniqueness. -/
namespace Markov

def t1_vietaParent (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (min t.1 (3*t.1*t.2.1-t.2.2), max t.1 (3*t.1*t.2.1-t.2.2), t.2.1)

theorem t1_vietaParent_left (p q r : ℕ) (h : IsOrderedTriple p q r) :
    t1_vietaParent (t1_vietaLeft (p,q,r)) = (p,q,r) := by
  have hpr : r ≤ p*r := by nlinarith [h.1]
  have hq : q ≤ 3*p*r := by nlinarith [h.2.2.1]
  simp only [t1_vietaParent, t1_vietaLeft]
  rw [Nat.sub_sub_self hq, min_eq_left h.2.1, max_eq_right h.2.1]

theorem t1_vietaParent_right (p q r : ℕ) (h : IsOrderedTriple p q r) :
    t1_vietaParent (t1_vietaRight (p,q,r)) = (p,q,r) := by
  have hqpos := h.1.trans_le h.2.1
  have hqr : r ≤ q*r := by nlinarith
  have hp : p ≤ 3*q*r := by nlinarith [h.2.1, h.2.2.1]
  simp only [t1_vietaParent, t1_vietaRight]
  rw [Nat.sub_sub_self hp, min_eq_right h.2.1, max_eq_left h.2.1]

theorem t1_vietaSuccessor_parent {s t : ℕ × ℕ × ℕ}
    (hs : IsOrderedTriple s.1 s.2.1 s.2.2) (hst : t1_vietaSuccessor s t) :
    t1_vietaParent t = s := by
  rcases s with ⟨p,q,r⟩
  rcases hst with rfl | rfl
  · exact t1_vietaParent_left p q r hs
  · exact t1_vietaParent_right p q r hs

theorem t1_vietaSuccessor_unique_parent {s s' t : ℕ × ℕ × ℕ}
    (hs : IsOrderedTriple s.1 s.2.1 s.2.2)
    (hs' : IsOrderedTriple s'.1 s'.2.1 s'.2.2)
    (hst : t1_vietaSuccessor s t) (hs't : t1_vietaSuccessor s' t) : s = s' :=
  (t1_vietaSuccessor_parent hs hst).symm.trans (t1_vietaSuccessor_parent hs' hs't)

theorem t1_vietaChildren_distinct (p q r : ℕ) (hpq : p < q) :
    t1_vietaLeft (p,q,r) ≠ t1_vietaRight (p,q,r) := by
  intro he
  have := congrArg Prod.fst he
  simp only [t1_vietaLeft, t1_vietaRight] at this
  omega

end Markov
