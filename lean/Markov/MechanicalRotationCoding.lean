import Markov.FareyMechanicalWords
import Mathlib.Data.List.Rotate

/-! The explicit quotient-defined lower mechanical word is exactly the
threshold coding of rotation by q modulo p+q, including every literal cyclic
phase. These are identities of concrete lists, not an assumed geometric
rotation model or a curve-classification premise. -/

namespace Markov

/-- A quotient jump is exactly the second-letter interval of the literal
rotation state k*q modulo p+q. Pure horizontal and vertical directions are
included; only the zero-length case is excluded. -/
theorem lowerMechanicalLetter_mod (p q k : ℕ) (hn : 0 < p + q) :
    lowerMechanicalLetter p q k = decide (p ≤ (k * q) % (p + q)) := by
  let n := p + q
  let r := (k * q) % n
  let t := k * q / n
  have hsplit : (k + 1) * q = (r + q) + n * t := by
    have h := Nat.mod_add_div (k * q) n
    change r + n * t = k * q at h
    calc
      (k + 1) * q = k * q + q := by ring
      _ = (r + n * t) + q := by rw [h]
      _ = (r + q) + n * t := by omega
  have hnext : (k + 1) * q / n = (r + q) / n + t := by
    rw [hsplit, Nat.add_mul_div_left _ _ hn]
  have hiff : k * q / n < (k + 1) * q / n ↔ p ≤ r := by
    rw [hnext]
    change t < (r + q) / n + t ↔ p ≤ r
    constructor
    · intro h
      have hv : 1 ≤ (r + q) / n := by omega
      have hm := (Nat.le_div_iff_mul_le hn).mp hv
      change 1 * (p + q) ≤ r + q at hm
      omega
    · intro h
      have hm : 1 * n ≤ r + q := by dsimp [n]; omega
      have hv : 1 ≤ (r + q) / n := (Nat.le_div_iff_mul_le hn).mpr hm
      omega
  unfold lowerMechanicalLetter
  exact decide_eq_decide.mpr hiff

/-- Reducing the step index modulo the actual word length preserves its
literal letter, with no coprimality assumption. -/
theorem lowerMechanicalLetter_period_mod (p q k : ℕ) (hn : 0 < p + q) :
    lowerMechanicalLetter p q (k % (p + q)) = lowerMechanicalLetter p q k := by
  rw [lowerMechanicalLetter_mod p q _ hn, lowerMechanicalLetter_mod p q _ hn,
    Nat.mod_mul_mod]

/-- The explicit threshold coding of rotation by q from step-phase r. -/
def lowerMechanicalRotationCode (p q r : ℕ) : List Bool :=
  (List.range (p + q)).map (fun i => decide (p ≤ ((r + i) * q) % (p + q)))

/-- List rotation agrees with modular-state threshold coding. The
mechanical word construction uses this coding to compare cyclic words. -/
theorem lowerMechanicalWord_rotate_eq_code (p q r : ℕ) (hn : 0 < p + q) :
    (lowerMechanicalWord p q).rotate r = lowerMechanicalRotationCode p q r := by
  apply List.ext_getElem
  · simp only [List.length_rotate, lowerMechanicalWord_length,
      lowerMechanicalRotationCode, List.length_map, List.length_range]
  · intro i hi hj
    rw [List.getElem_rotate]
    simp only [lowerMechanicalWord, lowerMechanicalRotationCode, List.getElem_map,
      List.getElem_range, List.length_map, List.length_range]
    rw [lowerMechanicalLetter_mod p q _ hn, Nat.mod_mul_mod, Nat.add_comm i r]

end Markov
