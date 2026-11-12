import T1FareyTraceOrder
import T1FrickeNumbers
import T1MarkovChildren

/-! The actual ordered Markov triple of a fundamental-sector Farey word.
Its entries are the original integer matrix traces divided by three. -/
namespace Markov

def t1_fareyWordTriple (w : List Bool) : ℕ × ℕ × ℕ :=
  let M := (t1_fareyWordMatrices w).1
  let N := (t1_fareyWordMatrices w).2
  (min (t1_traceNumber M) (t1_traceNumber N),
    max (t1_traceNumber M) (t1_traceNumber N), t1_traceNumber (M*N))

theorem t1_fareyWord_number_order (w : List Bool) :
    t1_traceNumber (t1_fareyWordMatrices w).1 ≠ t1_traceNumber (t1_fareyWordMatrices w).2 ∧
    t1_traceNumber (t1_fareyWordMatrices w).1 <
      t1_traceNumber ((t1_fareyWordMatrices w).1 * (t1_fareyWordMatrices w).2) ∧
    t1_traceNumber (t1_fareyWordMatrices w).2 <
      t1_traceNumber ((t1_fareyWordMatrices w).1 * (t1_fareyWordMatrices w).2) := by
  have hp := (t1_fareyWord_holonomy w).positiveFrickePair
  have ht := t1_fareyWord_trace_order w
  have ha := (t1_traceNumber_spec _ hp.trace_left hp.three_left).1
  have hb := (t1_traceNumber_spec _ hp.trace_right hp.three_right).1
  have hc := (t1_traceNumber_spec _ hp.trace_product hp.three_product).1
  rw [ha,hb,hc] at ht
  constructor
  · intro he
    apply ht.1
    rw [he]
  · constructor <;> omega

theorem t1_fareyWordTriple_ordered (w : List Bool) :
    IsOrderedTriple (t1_fareyWordTriple w).1 (t1_fareyWordTriple w).2.1
      (t1_fareyWordTriple w).2.2 := by
  have hn := t1_positiveFricke_numbers (t1_fareyWord_holonomy w).positiveFrickePair
  have ho := t1_fareyWord_number_order w
  unfold t1_fareyWordTriple
  dsimp only
  by_cases hab : t1_traceNumber (t1_fareyWordMatrices w).1 ≤
      t1_traceNumber (t1_fareyWordMatrices w).2
  · rw [min_eq_left hab,max_eq_right hab]
    exact ⟨hn.1,hab,ho.2.2.le,hn.2.2.2⟩
  · have hba := le_of_lt (lt_of_not_ge hab)
    rw [min_eq_right hba,max_eq_left hba]
    exact ⟨hn.2.1,hba,ho.2.1.le,by nlinarith [hn.2.2.2]⟩

theorem t1_fareyWordTriple_strict (w : List Bool) :
    (t1_fareyWordTriple w).1 < (t1_fareyWordTriple w).2.1 ∧
      (t1_fareyWordTriple w).2.1 < (t1_fareyWordTriple w).2.2 := by
  have ho := t1_fareyWord_number_order w
  unfold t1_fareyWordTriple
  dsimp only
  by_cases hab : t1_traceNumber (t1_fareyWordMatrices w).1 ≤
      t1_traceNumber (t1_fareyWordMatrices w).2
  · rw [min_eq_left hab,max_eq_right hab]
    exact ⟨lt_of_le_of_ne hab ho.1,ho.2.2⟩
  · have hba := lt_of_not_ge hab
    rw [min_eq_right hba.le,max_eq_left hba.le]
    exact ⟨hba,ho.2.1⟩

theorem t1_fareyWordTriple_nil : t1_fareyWordTriple [] = (1,2,5) := by
  norm_num [t1_fareyWordTriple,t1_fareyWordMatrices,t1_traceNumber,
    modularGeneratorA,modularGeneratorB,Matrix.trace,Matrix.diag_apply,
    Matrix.mul_apply,Fin.sum_univ_two]
  decide

theorem t1_fareyWordTriple_left (w : List Bool) :
    t1_fareyWordTriple (false::w) =
      if t1_traceNumber (t1_fareyWordMatrices w).1 ≤
          t1_traceNumber (t1_fareyWordMatrices w).2
      then t1_vietaLeft (t1_fareyWordTriple w)
      else t1_vietaRight (t1_fareyWordTriple w) := by
  have hp := (t1_fareyWord_holonomy w).positiveFrickePair
  have ho := t1_fareyWord_number_order w
  rw [t1_fareyWordTriple]
  simp only [t1_fareyWordMatrices]
  rw [min_eq_left ho.2.1.le,max_eq_right ho.2.1.le,t1_traceNumber_left_move hp]
  by_cases hab : t1_traceNumber (t1_fareyWordMatrices w).1 ≤
      t1_traceNumber (t1_fareyWordMatrices w).2
  · simp only [hab,ite_true,t1_vietaLeft,t1_fareyWordTriple,
      min_eq_left hab,max_eq_right hab]
  · have hba := le_of_lt (lt_of_not_ge hab)
    simp only [hab,ite_false,t1_vietaRight,t1_fareyWordTriple,
      min_eq_right hba,max_eq_left hba]

theorem t1_fareyWordTriple_right (w : List Bool) :
    t1_fareyWordTriple (true::w) =
      if t1_traceNumber (t1_fareyWordMatrices w).1 ≤
          t1_traceNumber (t1_fareyWordMatrices w).2
      then t1_vietaRight (t1_fareyWordTriple w)
      else t1_vietaLeft (t1_fareyWordTriple w) := by
  have hp := (t1_fareyWord_holonomy w).positiveFrickePair
  have ho := t1_fareyWord_number_order w
  rw [t1_fareyWordTriple]
  simp only [t1_fareyWordMatrices]
  rw [min_eq_right ho.2.2.le,max_eq_left ho.2.2.le,t1_traceNumber_right_move hp]
  by_cases hab : t1_traceNumber (t1_fareyWordMatrices w).1 ≤
      t1_traceNumber (t1_fareyWordMatrices w).2
  · simp only [hab,ite_true,t1_vietaRight,t1_fareyWordTriple,
      min_eq_left hab,max_eq_right hab]
  · have hba := le_of_lt (lt_of_not_ge hab)
    simp only [hab,ite_false,t1_vietaLeft,t1_fareyWordTriple,
      min_eq_right hba,max_eq_left hba]

end Markov
