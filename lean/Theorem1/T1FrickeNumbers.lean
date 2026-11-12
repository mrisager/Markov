import Markov.FrickeUpperBranch
import Markov.Basic

/-! Canonical natural Markov numbers obtained from the actual integral
matrix traces, with no rounding or Diophantine correspondence premise. -/
namespace Markov

def t1_traceNumber (M : IntMatrixTwo) : ℕ := (M.trace / 3).toNat

theorem t1_traceNumber_spec (M : IntMatrixTwo) (hpos : 3 ≤ M.trace)
    (hd : 3 ∣ M.trace) : M.trace = 3 * (t1_traceNumber M : ℤ) ∧ 0 < t1_traceNumber M := by
  obtain ⟨a,ha⟩ := hd
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 ≤ a := by omega
  have he : t1_traceNumber M = a.toNat := by simp [t1_traceNumber,ha]
  rw [he]
  constructor
  · rw [Int.toNat_of_nonneg ha0]; exact ha
  · have hpos : (0 : ℤ) < (a.toNat : ℤ) := by
      rw [Int.toNat_of_nonneg ha0]
      omega
    exact_mod_cast hpos

theorem t1_positiveFricke_numbers {M N : IntMatrixTwo} (h : PositiveFrickePair M N) :
    0 < t1_traceNumber M ∧ 0 < t1_traceNumber N ∧ 0 < t1_traceNumber (M*N) ∧
      (t1_traceNumber M)^2 + (t1_traceNumber N)^2 + (t1_traceNumber (M*N))^2 =
        3 * t1_traceNumber M * t1_traceNumber N * t1_traceNumber (M*N) := by
  obtain ⟨ha,hapos⟩ := t1_traceNumber_spec M h.trace_left h.three_left
  obtain ⟨hb,hbpos⟩ := t1_traceNumber_spec N h.trace_right h.three_right
  obtain ⟨hc,hcpos⟩ := t1_traceNumber_spec (M*N) h.trace_product h.three_product
  refine ⟨hapos,hbpos,hcpos,?_⟩
  have he := h.fricke
  rw [ha,hb,hc] at he
  have heZ : (t1_traceNumber M : ℤ)^2 + (t1_traceNumber N : ℤ)^2 +
      (t1_traceNumber (M*N) : ℤ)^2 =
      3 * (t1_traceNumber M : ℤ) * t1_traceNumber N * t1_traceNumber (M*N) := by
    nlinarith only [he]
  exact_mod_cast heZ

theorem t1_traceNumber_left_move {M N : IntMatrixTwo} (h : PositiveFrickePair M N) :
    t1_traceNumber (M*(M*N)) =
      3 * t1_traceNumber M * t1_traceNumber (M*N) - t1_traceNumber N := by
  have ha := (t1_traceNumber_spec M h.trace_left h.three_left).1
  have hb := (t1_traceNumber_spec N h.trace_right h.three_right).1
  have hc := (t1_traceNumber_spec (M*N) h.trace_product h.three_product).1
  have hd := (t1_traceNumber_spec (M*(M*N)) h.left.trace_product h.left.three_product).1
  have ht := matrix_trace_left_move M N h.det_left
  rw [ha,hb,hc,hd] at ht
  have heZ : (t1_traceNumber (M*(M*N)) : ℤ) + t1_traceNumber N =
      3 * (t1_traceNumber M : ℤ) * t1_traceNumber (M*N) := by nlinarith only [ht]
  have he : t1_traceNumber (M*(M*N)) + t1_traceNumber N =
      3 * t1_traceNumber M * t1_traceNumber (M*N) := by exact_mod_cast heZ
  omega

theorem t1_traceNumber_right_move {M N : IntMatrixTwo} (h : PositiveFrickePair M N) :
    t1_traceNumber ((M*N)*N) =
      3 * t1_traceNumber N * t1_traceNumber (M*N) - t1_traceNumber M := by
  have ha := (t1_traceNumber_spec M h.trace_left h.three_left).1
  have hb := (t1_traceNumber_spec N h.trace_right h.three_right).1
  have hc := (t1_traceNumber_spec (M*N) h.trace_product h.three_product).1
  have hd := (t1_traceNumber_spec ((M*N)*N) h.right.trace_product h.right.three_product).1
  have ht := matrix_trace_right_move M N h.det_right
  rw [ha,hb,hc,hd] at ht
  have heZ : (t1_traceNumber ((M*N)*N) : ℤ) + t1_traceNumber M =
      3 * (t1_traceNumber N : ℤ) * t1_traceNumber (M*N) := by nlinarith only [ht]
  have he : t1_traceNumber ((M*N)*N) + t1_traceNumber M =
      3 * t1_traceNumber N * t1_traceNumber (M*N) := by exact_mod_cast heZ
  omega

end Markov
