import Markov.MechanicalCanonicalWords
import Markov.PaperAxisCellWordH1
import Mathlib.Data.List.Count

/-! Counts and the original marked additive coordinates of the explicit
mechanical lists. This supplies coordinates only after a literal word identity;
it does not infer any geometric or nonabelian class from homology. -/

namespace Markov

private theorem mechanical_quotient_step (p q n : ℕ) (hn : 0 < p+q) :
    n*q/(p+q) ≤ (n+1)*q/(p+q) ∧
      (n+1)*q/(p+q) ≤ n*q/(p+q)+1 := by
  have hlo : n*q/(p+q) ≤ (n+1)*q/(p+q) :=
    Nat.div_le_div_right (Nat.mul_le_mul_right q (Nat.le_succ n))
  have hm := Nat.mod_lt (n*q) hn
  have hs := Nat.mod_add_div (n*q) (p+q)
  have hupper : (n+1)*q < (n*q/(p+q)+2)*(p+q) := by nlinarith
  have h := (Nat.div_lt_iff_lt_mul hn).mpr hupper
  exact ⟨hlo, by omega⟩

private theorem mechanical_true_prefix (p q n : ℕ) (hn : 0 < p+q) :
    (((List.range n).map (lowerMechanicalLetter p q)).count true) =
      n*q/(p+q) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hh := mechanical_quotient_step p q n hn
      rw [List.range_succ, List.map_append, List.map_singleton, List.count_append, ih]
      by_cases h : n*q/(p+q) < (n+1)*q/(p+q)
      · norm_num [lowerMechanicalLetter, h]
        omega
      · simp only [lowerMechanicalLetter, h, decide_false, List.count_singleton]
        norm_num
        omega

/-- The explicit quotient word has exactly q second-seed letters. -/
theorem lowerMechanicalWord_count_true (p q : ℕ) (hn : 0 < p+q) :
    (lowerMechanicalWord p q).count true = q := by
  have h := mechanical_true_prefix p q (p+q) hn
  simpa only [lowerMechanicalWord, Nat.mul_div_cancel_left _ hn] using h

private theorem bool_counts_length (l : List Bool) :
    l.count false+l.count true = l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
      cases b <;> simp only [List.count_cons, List.length_cons] <;> norm_num <;> omega

/-- The explicit quotient word has exactly p first-seed letters. -/
theorem lowerMechanicalWord_count_false (p q : ℕ) (hn : 0 < p+q) :
    (lowerMechanicalWord p q).count false = p := by
  have h := bool_counts_length (lowerMechanicalWord p q)
  rw [lowerMechanicalWord_count_true p q hn, lowerMechanicalWord_length] at h
  omega

private theorem bool_sum_weights (l : List Bool) (x y : ℤ × ℤ) :
    (l.map (fun b => if b then y else x)).sum = l.count false • x+l.count true • y := by
  induction l with
  | nil => simp
  | cons b l ih =>
      cases b <;> simp only [List.map_cons, List.sum_cons, ih, List.count_cons] <;>
        norm_num [add_nsmul] <;> ring

/-- The explicit signed mechanical list has its exact ORIGINAL A/B sum.
No primitivity premise is used to compute these actual coordinates. -/
theorem quadrantLowerMechanicalSideWord_coordinate_sum
    (k : Fin 4) (p q : ℕ) (hn : 0 < p+q) :
    ((quadrantLowerMechanicalSideWord k p q).map paperAxisCellLetterCoordinates).sum =
      p • paperAxisCellLetterCoordinates k +
        q • paperAxisCellLetterCoordinates (paperQuadrilateralNextSide k) := by
  unfold quadrantLowerMechanicalSideWord
  rw [List.map_map]
  simp only [Function.comp_def]
  have he : (fun b : Bool => paperAxisCellLetterCoordinates
      (if b then paperQuadrilateralNextSide k else k)) =
      (fun b : Bool => if b then paperAxisCellLetterCoordinates (paperQuadrilateralNextSide k)
        else paperAxisCellLetterCoordinates k) := by
    funext b
    cases b <;> rfl
  rw [he, bool_sum_weights, lowerMechanicalWord_count_false p q hn,
    lowerMechanicalWord_count_true p q hn]

end Markov
