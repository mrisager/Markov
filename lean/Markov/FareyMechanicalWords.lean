import Markov.SeedCanonical
import Mathlib.Data.List.Range

/-! Literal lower mechanical binary words and their exact Farey concatenation.
False denotes the first seed letter and true the second. These words are
defined by adjacent integer quotients, independently of any curve or matching.
The determinant-one recursion is proved arithmetically, not supplied as a
normal-form/classification hypothesis. -/

namespace Markov

/-- The actual second-letter crossing detected by adjacent integer quotients. -/
def lowerMechanicalLetter (p q k : ℕ) : Bool :=
  decide (k * q / (p + q) < (k + 1) * q / (p + q))

/-- The explicit lower mechanical word with p first-seed and q second-seed
crossings. Its length is p+q, with no primitivity assumption in the definition. -/
def lowerMechanicalWord (p q : ℕ) : List Bool :=
  (List.range (p + q)).map (lowerMechanicalLetter p q)

theorem lowerMechanicalWord_length (p q : ℕ) :
    (lowerMechanicalWord p q).length = p + q := by
  simp only [lowerMechanicalWord, List.length_map, List.length_range]

theorem lowerMechanicalWord_seed_left : lowerMechanicalWord 1 0 = [false] := by decide

theorem lowerMechanicalWord_seed_right : lowerMechanicalWord 0 1 = [true] := by decide

private theorem close_quotients
    (m n x y e : ℕ) (hm : 0 < m) (hmn : m < n) (he : e ≤ m)
    (hcross : m * x = n * y + e) : x / n = y / m := by
  let t := y / m
  let r := y % m
  have hr : r < m := Nat.mod_lt y hm
  have hy : r + m * t = y := Nat.mod_add_div y m
  have hid : m * x = m * (t * n) + (n * r + e) := by
    rw [hcross, ← hy]
    ring
  have hlo : t * n ≤ x := by
    apply Nat.le_of_mul_le_mul_left (c := m) _ hm
    rw [hid]
    exact Nat.le_add_right _ _
  have hrem : n * r + e < n * m := by
    calc
      n * r + e < n * r + n := Nat.add_lt_add_left (lt_of_le_of_lt he hmn) _
      _ = n * (r + 1) := by ring
      _ ≤ n * m := Nat.mul_le_mul_left n (by omega)
  have hhi : x < (t + 1) * n := by
    apply Nat.lt_of_mul_lt_mul_left (a := m)
    calc
      m * x = m * (t * n) + (n * r + e) := hid
      _ < m * (t * n) + n * m := Nat.add_lt_add_left hrem _
      _ = m * ((t + 1) * n) := by ring
  exact Nat.div_eq_of_lt_le hlo hhi

private theorem farey_masses_pos (a b c d : ℕ) (hd : a * d = b * c + 1) :
    0 < a + b ∧ 0 < c + d := by
  constructor
  · by_contra hn
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    simp [ha, hb] at hd
  · by_contra hn
    have hc : c = 0 := by omega
    have hd' : d = 0 := by omega
    simp [hc, hd'] at hd

/-- Determinant one makes every quotient in the first Farey segment exactly
the corresponding parent quotient, including the shared endpoint. -/
theorem fareyLowerMechanical_quotient_prefix
    (a b c d k : ℕ) (hd : a * d = b * c + 1) (hk : k ≤ a + b) :
    k * (b + d) / ((a + c) + (b + d)) = k * b / (a + b) := by
  have hpos := farey_masses_pos a b c d hd
  have hcross0 : (a + b) * (b + d) = ((a + c) + (b + d)) * b + 1 := by
    nlinarith [hd]
  apply close_quotients (a + b) ((a + c) + (b + d))
    (k * (b + d)) (k * b) k hpos.1 (by omega) hk
  calc
    (a + b) * (k * (b + d)) = k * ((a + b) * (b + d)) := by ring
    _ = k * (((a + c) + (b + d)) * b + 1) := by rw [hcross0]
    _ = ((a + c) + (b + d)) * (k * b) + k := by ring

/-- The second Farey segment's quotients equal the second parent's quotients
plus the exact first-parent vertical count. This includes both endpoints. -/
theorem fareyLowerMechanical_quotient_suffix
    (a b c d j : ℕ) (hd : a * d = b * c + 1) (hj : j ≤ c + d) :
    ((a + b) + j) * (b + d) / ((a + c) + (b + d)) =
      b + j * d / (c + d) := by
  have hpos := farey_masses_pos a b c d hd
  let m := a + b
  let l := c + d
  let n := (a + c) + (b + d)
  let q := b + d
  have hmn : m < n := by dsimp [m, n]; omega
  have hln : l < n := by dsimp [l, n]; omega
  have hm : m * q = n * b + 1 := by dsimp [m, q, n]; nlinarith [hd]
  have hl : l * q + 1 = n * d := by dsimp [l, q, n]; nlinarith [hd]
  have hjl : j ≤ l := hj
  have hmul : j * (l * q) + j = j * (n * d) := by
    simpa only [Nat.mul_add, Nat.mul_one] using congrArg (fun x => j * x) hl
  have hcross : l * (1 + j * q) = n * (j * d) + (l - j) := by
    calc
      l * (1 + j * q) = l + j * (l * q) := by ring
      _ = j * (l * q) + j + (l - j) := by omega
      _ = j * (n * d) + (l - j) := by rw [hmul]
      _ = n * (j * d) + (l - j) := by ring
  have hquot : (1 + j * q) / n = j * d / l :=
    close_quotients l n (1 + j * q) (j * d) (l - j) hpos.2 hln
      (Nat.sub_le l j) hcross
  have hsplit : (m + j) * q = (1 + j * q) + n * b := by
    calc
      (m + j) * q = m * q + j * q := by ring
      _ = (n * b + 1) + j * q := by rw [hm]
      _ = (1 + j * q) + n * b := by ring
  change (m + j) * q / n = b + j * d / l
  rw [hsplit, Nat.add_mul_div_left _ _ (by omega : 0 < n), hquot, Nat.add_comm]

private theorem farey_letter_prefix
    (a b c d k : ℕ) (hd : a * d = b * c + 1) (hk : k < a + b) :
    lowerMechanicalLetter (a + c) (b + d) k = lowerMechanicalLetter a b k := by
  unfold lowerMechanicalLetter
  rw [fareyLowerMechanical_quotient_prefix a b c d k hd (by omega),
    fareyLowerMechanical_quotient_prefix a b c d (k + 1) hd (by omega)]

private theorem farey_letter_suffix
    (a b c d j : ℕ) (hd : a * d = b * c + 1) (hj : j < c + d) :
    lowerMechanicalLetter (a + c) (b + d) ((a + b) + j) =
      lowerMechanicalLetter c d j := by
  unfold lowerMechanicalLetter
  have hs : (a + b + j) + 1 = (a + b) + (j + 1) := by omega
  rw [hs, fareyLowerMechanical_quotient_suffix a b c d j hd (by omega),
    fareyLowerMechanical_quotient_suffix a b c d (j + 1) hd (by omega)]
  simp only [Nat.add_lt_add_iff_left]

/-- The explicit lower mechanical words satisfy EXACTLY the literal Farey
concatenation used by the actual SeededFarey matrix recursion. No cyclic word
normal form, homology classification or unspecified word witness is assumed. -/
theorem lowerMechanicalWord_farey_concat
    (a b c d : ℕ) (hd : a * d = b * c + 1) :
    lowerMechanicalWord (a + c) (b + d) =
      lowerMechanicalWord a b ++ lowerMechanicalWord c d := by
  have hmass : (a + c) + (b + d) = (a + b) + (c + d) := by omega
  unfold lowerMechanicalWord
  rw [hmass, List.range_add, List.map_append, List.map_map]
  refine congrArg₂ (fun x y : List Bool => x ++ y) ?_ ?_
  · apply List.map_congr_left
    intro k hk
    exact farey_letter_prefix a b c d k hd (List.mem_range.mp hk)
  · apply List.map_congr_left
    intro j hj
    exact farey_letter_suffix a b c d j hd (List.mem_range.mp hj)

end Markov
