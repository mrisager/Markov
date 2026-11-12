import T1FareyWords

/-! Strict trace ordering for the actual fundamental-sector words. The
root traces are 3, 6, 15 in the original marking. -/
namespace Markov

theorem t1_fareyWord_seed_traces :
    (t1_fareyWordMatrices []).1.trace = 3 ∧
    (t1_fareyWordMatrices []).2.trace = 6 ∧
    ((t1_fareyWordMatrices []).1 * (t1_fareyWordMatrices []).2).trace = 15 := by
  norm_num [t1_fareyWordMatrices, modularGeneratorA, modularGeneratorB,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two]

private theorem t1_fricke_move_strict (a b c : ℤ) (ha : 3 ≤ a)
    (hc : 0 < c) (hbc : b < c) : c < a*c-b := by
  have hm : 0 ≤ (a-3)*c := mul_nonneg (by omega) hc.le
  nlinarith

theorem t1_fareyWord_trace_order (w : List Bool) :
    (t1_fareyWordMatrices w).1.trace ≠ (t1_fareyWordMatrices w).2.trace ∧
    (t1_fareyWordMatrices w).1.trace <
      ((t1_fareyWordMatrices w).1 * (t1_fareyWordMatrices w).2).trace ∧
    (t1_fareyWordMatrices w).2.trace <
      ((t1_fareyWordMatrices w).1 * (t1_fareyWordMatrices w).2).trace := by
  induction w with
  | nil =>
    rcases t1_fareyWord_seed_traces with ⟨h1,h2,h3⟩
    rw [h1,h2,h3]
    norm_num
  | cons b w ih =>
    let M := (t1_fareyWordMatrices w).1
    let N := (t1_fareyWordMatrices w).2
    have hp : PositiveFrickePair M N := (t1_fareyWord_holonomy w).positiveFrickePair
    have h1 : M.trace < (M*N).trace := ih.2.1
    have h2 : N.trace < (M*N).trace := ih.2.2
    cases b with
    | false =>
      change M.trace ≠ (M*N).trace ∧ M.trace < (M*(M*N)).trace ∧
        (M*N).trace < (M*(M*N)).trace
      rw [matrix_trace_left_move M N hp.det_left]
      have hc := t1_fricke_move_strict M.trace N.trace (M*N).trace hp.trace_left
        (by linarith [hp.trace_product]) h2
      exact ⟨ne_of_lt h1,h1.trans hc,hc⟩
    | true =>
      change (M*N).trace ≠ N.trace ∧ (M*N).trace < ((M*N)*N).trace ∧
        N.trace < ((M*N)*N).trace
      rw [matrix_trace_right_move M N hp.det_right]
      have hc := t1_fricke_move_strict N.trace M.trace (M*N).trace hp.trace_right
        (by linarith [hp.trace_product]) h1
      exact ⟨ne_of_gt h2,hc,h2.trans hc⟩

end Markov
