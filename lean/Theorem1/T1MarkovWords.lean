import T1MarkovTreeParent

/-! Actual binary Vieta words rooted at the first nonexceptional triple.
All triples are represented by their full three coordinates. -/
namespace Markov

def t1_markovWord : List Bool → ℕ × ℕ × ℕ
  | [] => (1,2,5)
  | false :: w => t1_vietaLeft (t1_markovWord w)
  | true :: w => t1_vietaRight (t1_markovWord w)

theorem t1_markovWord_ordered (w : List Bool) :
    IsOrderedTriple (t1_markovWord w).1 (t1_markovWord w).2.1 (t1_markovWord w).2.2 := by
  induction w with
  | nil => decide
  | cons b w ih =>
    cases b with
    | false => exact t1_vietaSuccessor_preserves_ordered ih (Or.inl rfl)
    | true => exact t1_vietaSuccessor_preserves_ordered ih (Or.inr rfl)

theorem t1_markovWord_strict (w : List Bool) :
    (t1_markovWord w).1 < (t1_markovWord w).2.1 ∧
      (t1_markovWord w).2.1 < (t1_markovWord w).2.2 := by
  induction w with
  | nil => decide
  | cons b w ih =>
    have ho := t1_markovWord_ordered w
    rcases hstate : t1_markovWord w with ⟨p,q,r⟩
    simp only [hstate] at ih ho
    cases b with
    | false =>
      simpa only [t1_markovWord,hstate,t1_vietaLeft] using
        (show p < r ∧ r < 3*p*r-q from
          ⟨ih.1.trans ih.2, (t1_ordered_markov_left_child p q r ho).2⟩)
    | true =>
      simpa only [t1_markovWord,hstate,t1_vietaRight] using
        (show q < r ∧ r < 3*q*r-p from
          ⟨ih.2, (t1_ordered_markov_right_child p q r ho).2⟩)

theorem t1_markovWord_height_ge (w : List Bool) : 5 ≤ (t1_markovWord w).2.2 := by
  induction w with
  | nil => decide
  | cons b w ih =>
    have ho := t1_markovWord_ordered w
    rcases hstate : t1_markovWord w with ⟨p,q,r⟩
    simp only [hstate] at ho ih
    cases b with
    | false => simpa only [t1_markovWord,hstate,t1_vietaLeft] using
        ih.trans (t1_ordered_markov_left_child p q r ho).2.le
    | true => simpa only [t1_markovWord,hstate,t1_vietaRight] using
        ih.trans (t1_ordered_markov_right_child p q r ho).2.le

theorem t1_markovWord_parent_cons (b : Bool) (w : List Bool) :
    t1_vietaParent (t1_markovWord (b::w)) = t1_markovWord w := by
  have ho := t1_markovWord_ordered w
  rcases hstate : t1_markovWord w with ⟨p,q,r⟩
  simp only [hstate] at ho
  cases b with
  | false => simpa only [t1_markovWord,hstate] using t1_vietaParent_left p q r ho
  | true => simpa only [t1_markovWord,hstate] using t1_vietaParent_right p q r ho

theorem t1_markovWord_cons_ne_nil (b : Bool) (w : List Bool) :
    t1_markovWord (b::w) ≠ t1_markovWord [] := by
  have hge := t1_markovWord_height_ge w
  have ho := t1_markovWord_ordered w
  rcases hstate : t1_markovWord w with ⟨p,q,r⟩
  simp only [hstate] at ho hge
  intro he
  have hr := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) he
  cases b with
  | false =>
    have hr' : 3*p*r-q = 5 := by
      simpa only [t1_markovWord,hstate,t1_vietaLeft] using hr
    have hi := (t1_ordered_markov_left_child p q r ho).2
    omega
  | true =>
    have hr' : 3*q*r-p = 5 := by
      simpa only [t1_markovWord,hstate,t1_vietaRight] using hr
    have hi := (t1_ordered_markov_right_child p q r ho).2
    omega

theorem t1_markovWord_injective : Function.Injective t1_markovWord := by
  intro w
  induction w with
  | nil =>
    intro v he
    cases v with
    | nil => rfl
    | cons b v => exact (t1_markovWord_cons_ne_nil b v he.symm).elim
  | cons b w ih =>
    intro v he
    cases v with
    | nil => exact (t1_markovWord_cons_ne_nil b w he).elim
    | cons c v =>
      have hp := congrArg t1_vietaParent he
      rw [t1_markovWord_parent_cons, t1_markovWord_parent_cons] at hp
      have hwv := ih hp
      subst v
      have hs := (t1_markovWord_strict w).1
      rcases hstate : t1_markovWord w with ⟨p,q,r⟩
      simp only [hstate] at hs
      cases b <;> cases c
      · rfl
      · exact (t1_vietaChildren_distinct p q r hs (by simpa only [t1_markovWord,hstate] using he)).elim
      · exact (t1_vietaChildren_distinct p q r hs (by simpa only [t1_markovWord,hstate] using he.symm)).elim
      · rfl

theorem t1_markovGenerated_exception_or_word {t : ℕ × ℕ × ℕ}
    (hg : t1_markovGenerated t) :
    t = (1,1,1) ∨ t = (1,1,2) ∨ ∃ w : List Bool, t1_markovWord w = t := by
  induction hg with
  | refl => exact Or.inl rfl
  | @tail t t' hpath hstep ih =>
    rcases ih with hroot | hsecond | ⟨w,hw⟩
    · subst t
      rcases hstep with rfl | rfl <;> exact Or.inr (Or.inl rfl)
    · subst t
      rcases hstep with rfl | rfl <;> exact Or.inr (Or.inr ⟨[],rfl⟩)
    · rw [← hw] at hstep
      rcases hstep with rfl | rfl
      · exact Or.inr (Or.inr ⟨false::w,rfl⟩)
      · exact Or.inr (Or.inr ⟨true::w,rfl⟩)

theorem t1_ordered_markov_exception_or_word (p q r : ℕ) (h : IsOrderedTriple p q r) :
    (p,q,r) = (1,1,1) ∨ (p,q,r) = (1,1,2) ∨
      ∃ w : List Bool, t1_markovWord w = (p,q,r) :=
  t1_markovGenerated_exception_or_word (t1_all_ordered_markov_generated r p q h)

end Markov
