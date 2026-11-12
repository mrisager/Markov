import T1FareyTraceTriples
import T1MarkovWords

/-! Actual Farey/Vieta path correspondence. A branch is swapped precisely
when the two actual factor traces are in reverse order. -/
namespace Markov

def t1_fareyBranch (w : List Bool) (b : Bool) : Bool :=
  if t1_traceNumber (t1_fareyWordMatrices w).1 ≤
      t1_traceNumber (t1_fareyWordMatrices w).2 then b else !b

theorem t1_fareyBranch_involutive (w : List Bool) : Function.Involutive (t1_fareyBranch w) := by
  intro b
  unfold t1_fareyBranch
  split <;> simp

def t1_fareyToMarkovWord : List Bool → List Bool
  | [] => []
  | b::w => t1_fareyBranch w b :: t1_fareyToMarkovWord w

theorem t1_fareyToMarkovWord_injective : Function.Injective t1_fareyToMarkovWord := by
  intro w
  induction w with
  | nil =>
    intro v he
    cases v with
    | nil => rfl
    | cons c v => cases he
  | cons b w ih =>
    intro v he
    cases v with
    | nil => cases he
    | cons c v =>
      have he' : t1_fareyBranch w b = t1_fareyBranch v c ∧
          t1_fareyToMarkovWord w = t1_fareyToMarkovWord v := List.cons.inj he
      have hv := ih he'.2
      subst v
      have hb := (t1_fareyBranch_involutive w).injective he'.1
      exact congrArg (fun c => c::w) hb

theorem t1_fareyToMarkovWord_surjective : Function.Surjective t1_fareyToMarkovWord := by
  intro v
  induction v with
  | nil => exact ⟨[],rfl⟩
  | cons b v ih =>
    obtain ⟨w,hw⟩ := ih
    refine ⟨t1_fareyBranch w b :: w, ?_⟩
    simp only [t1_fareyToMarkovWord, t1_fareyBranch_involutive w b, hw]

theorem t1_fareyWordTriple_eq_markovWord (w : List Bool) :
    t1_fareyWordTriple w = t1_markovWord (t1_fareyToMarkovWord w) := by
  induction w with
  | nil => exact t1_fareyWordTriple_nil
  | cons b w ih =>
    cases b with
    | false =>
      rw [t1_fareyWordTriple_left]
      by_cases hab : t1_traceNumber (t1_fareyWordMatrices w).1 ≤
          t1_traceNumber (t1_fareyWordMatrices w).2
      · simp only [hab,ite_true,t1_fareyToMarkovWord,t1_fareyBranch,t1_markovWord,ih]
      · simp only [hab,ite_false,t1_fareyToMarkovWord,t1_fareyBranch,Bool.not_false,
          t1_markovWord,ih]
    | true =>
      rw [t1_fareyWordTriple_right]
      by_cases hab : t1_traceNumber (t1_fareyWordMatrices w).1 ≤
          t1_traceNumber (t1_fareyWordMatrices w).2
      · simp only [hab,ite_true,t1_fareyToMarkovWord,t1_fareyBranch,t1_markovWord,ih]
      · simp only [hab,ite_false,t1_fareyToMarkovWord,t1_fareyBranch,Bool.not_true,
          t1_markovWord,ih]

theorem t1_fareyWordTriple_injective : Function.Injective t1_fareyWordTriple := by
  intro w v he
  rw [t1_fareyWordTriple_eq_markovWord,t1_fareyWordTriple_eq_markovWord] at he
  exact t1_fareyToMarkovWord_injective (t1_markovWord_injective he)

theorem t1_ordered_markov_exception_or_farey_word (p q r : ℕ) (h : IsOrderedTriple p q r) :
    (p,q,r) = (1,1,1) ∨ (p,q,r) = (1,1,2) ∨
      ∃ w : List Bool, t1_fareyWordTriple w = (p,q,r) := by
  rcases t1_ordered_markov_exception_or_word p q r h with h1 | h2 | ⟨w,hw⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · obtain ⟨v,hv⟩ := t1_fareyToMarkovWord_surjective w
    exact Or.inr (Or.inr ⟨v,by rw [t1_fareyWordTriple_eq_markovWord,hv,hw]⟩)

end Markov
