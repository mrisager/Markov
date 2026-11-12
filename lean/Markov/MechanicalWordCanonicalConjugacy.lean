import Markov.MechanicalWordCounts
import Markov.PaperAxisBackwardCycleWord
import Mathlib.Algebra.Group.Conj

/-! Literal mechanical word identities plus primitive ORIGINAL signed sums
give genuine conjugacy in the actual deck subgroup to the existing canonical
word or its inverse. The correct label is chosen only after the list identity.
No primitive-canonical, H1-to-class or geometric normal-form field is assumed. -/

noncomputable section
namespace Markov

/-- The canonical quadrant label of a signed mechanical list is the NEGATIVE
of its literal original A/B sum. Exact counts compute its nonnegative
coordinates before any primitive/canonical word premise is used. -/
theorem quadrantLowerMechanicalSideWord_negative_sum_coordinates
    (k : Fin 4) (m n : ℕ) (hn : 0 < m + n) :
    quadrantCoordinates k
        (-((quadrantLowerMechanicalSideWord k m n).map paperAxisCellLetterCoordinates).sum) =
      ((m : ℤ), (n : ℤ)) := by
  rw [quadrantLowerMechanicalSideWord_coordinate_sum k m n hn]
  fin_cases k <;> ext <;>
    simp [quadrantCoordinates, paperAxisCellLetterCoordinates,
      paperQuadrilateralNextSide]

private theorem mechanical_canonical_for_label
    (k : Fin 4) (m n : ℕ) (v : ℤ × ℤ) (hp : IsCoprime v.1 v.2)
    (hcoords : quadrantCoordinates k v = ((m : ℤ), (n : ℤ))) :
    ∃ hv : NonnegativePrimitiveDirection (quadrantCoordinates k v),
      ((quadrantLowerMechanicalSideWord k m n).map paperQuadrilateralSideNeighbor).prod =
        quadrantPrimitiveTraceWord k v hv := by
  have hcop := quadrantCoordinates_coprime k v hp
  have hv : NonnegativePrimitiveDirection (quadrantCoordinates k v) :=
    ⟨by rw [hcoords]; change (0 : ℤ) ≤ (m : ℤ); exact_mod_cast (Nat.zero_le m),
      by rw [hcoords]; change (0 : ℤ) ≤ (n : ℤ); exact_mod_cast (Nat.zero_le n), hcop⟩
  refine ⟨hv, ?_⟩
  have h := quadrantPrimitiveTraceWord_eq_lowerMechanicalSideWord_prod k v hv
  rw [hcoords] at h
  simpa using h.symm

/-- A primitive ORIGINAL signed sum determines a valid nonnegative primitive
canonical label AFTER this literal mechanical list and its sum are known.
The resulting subgroup product equality is exact, not an H1 inference. -/
theorem quadrantLowerMechanicalSideWord_prod_eq_canonical_of_primitive
    (k : Fin 4) (m n : ℕ) (hn : 0 < m + n) (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2)
    (hsum : ((quadrantLowerMechanicalSideWord k m n).map paperAxisCellLetterCoordinates).sum = p) :
    ∃ hv : NonnegativePrimitiveDirection (quadrantCoordinates k (-p)),
      ((quadrantLowerMechanicalSideWord k m n).map paperQuadrilateralSideNeighbor).prod =
        quadrantPrimitiveTraceWord k (-p) hv := by
  have hc : quadrantCoordinates k (-p) = ((m : ℤ), (n : ℤ)) := by
    rw [← hsum]
    exact quadrantLowerMechanicalSideWord_negative_sum_coordinates k m n hn
  exact mechanical_canonical_for_label k m n (-p)
    (by simpa only [Prod.fst_neg, Prod.snd_neg] using hp.neg_neg) hc

private theorem sideWord_rotate_sum (w : List (Fin 4)) (r : ℕ) :
    (((w.rotate r).map paperAxisCellLetterCoordinates).sum) =
      (w.map paperAxisCellLetterCoordinates).sum := by
  rw [List.map_rotate]
  exact (List.rotate_perm (w.map paperAxisCellLetterCoordinates) r).sum_eq

private theorem sideWord_rotate_isConj (w : List (Fin 4)) (r : ℕ) :
    IsConj ((w.map paperQuadrilateralSideNeighbor).prod)
      (((w.rotate r).map paperQuadrilateralSideNeighbor).prod) := by
  let P := ((w.take (r % w.length)).map paperQuadrilateralSideNeighbor).prod
  have hs : (w.map paperQuadrilateralSideNeighbor).prod =
      P * ((w.drop (r % w.length)).map paperQuadrilateralSideNeighbor).prod := by
    dsimp only [P]
    rw [← List.prod_append, ← List.map_append, List.take_append_drop]
  apply isConj_iff.mpr
  refine ⟨P⁻¹, ?_⟩
  simp only [inv_inv]
  rw [List.rotate_eq_drop_append_take_mod, List.map_append, List.prod_append, hs]
  simp only [inv_mul_cancel_left, P]

/-- An ACTUAL literal forward rotation to a mechanical list gives genuine
subgroup conjugacy to the raw canonical word labelled by the NEGATIVE original
signed sum. Its required primitive-coordinate premise is derived internally. -/
theorem paperSideWord_forward_mechanical_rotation_isConj
    (w : List (Fin 4)) (r : ℕ) (k : Fin 4) (m n : ℕ) (hn : 0 < m + n)
    (hWord : w.rotate r = quadrantLowerMechanicalSideWord k m n)
    (hp : IsCoprime ((w.map paperAxisCellLetterCoordinates).sum).1
      ((w.map paperAxisCellLetterCoordinates).sum).2) :
    ∃ hv : NonnegativePrimitiveDirection
        (quadrantCoordinates k (-((w.map paperAxisCellLetterCoordinates).sum))),
      IsConj ((w.map paperQuadrilateralSideNeighbor).prod)
        (quadrantPrimitiveTraceWord k (-((w.map paperAxisCellLetterCoordinates).sum)) hv) := by
  have hsum : ((quadrantLowerMechanicalSideWord k m n).map paperAxisCellLetterCoordinates).sum =
      (w.map paperAxisCellLetterCoordinates).sum := by
    rw [← hWord]
    exact sideWord_rotate_sum w r
  obtain ⟨hv, hcan⟩ := quadrantLowerMechanicalSideWord_prod_eq_canonical_of_primitive
    k m n hn ((w.map paperAxisCellLetterCoordinates).sum) hp hsum
  refine ⟨hv, ?_⟩
  have h := sideWord_rotate_isConj w r
  rwa [hWord, hcan] at h

private theorem sideLetter_opposite_coordinates (k : Fin 4) :
    paperAxisCellLetterCoordinates (paperQuadrilateralOppositeSide k) =
      -paperAxisCellLetterCoordinates k := by
  fin_cases k <;> rfl

private theorem sideWord_opposite_sum (w : List (Fin 4)) :
    ((w.map paperQuadrilateralOppositeSide).map paperAxisCellLetterCoordinates).sum =
      -(w.map paperAxisCellLetterCoordinates).sum := by
  induction w with
  | nil => simp
  | cons k w ih =>
    simp only [List.map_cons, List.sum_cons, ih, sideLetter_opposite_coordinates, neg_add]

private theorem sideWord_opposite_reverse_prod (w : List (Fin 4)) :
    ((w.reverse.map paperQuadrilateralOppositeSide).map paperQuadrilateralSideNeighbor).prod =
      (w.map paperQuadrilateralSideNeighbor).prod⁻¹ := by
  have h := List.prod_inv_reverse (w.map paperQuadrilateralSideNeighbor)
  simpa only [List.map_reverse, List.map_map, Function.comp_def,
    paperQuadrilateralSideNeighbor_opposite_eq_inv] using h.symm

/-- The EXACT backwards convention is opposite(reverse(forward rotation)).
Its primitive ORIGINAL signed sum yields conjugacy of the original product
to the INVERSE raw canonical word labelled by that ORIGINAL sum. Reversal is
not identified with a canonical rotation and the two signs are not collapsed. -/
theorem paperSideWord_backward_mechanical_rotation_isConj_inverse
    (w : List (Fin 4)) (r : ℕ) (k : Fin 4) (m n : ℕ) (hn : 0 < m + n)
    (hWord : (w.rotate r).reverse.map paperQuadrilateralOppositeSide =
      quadrantLowerMechanicalSideWord k m n)
    (hp : IsCoprime ((w.map paperAxisCellLetterCoordinates).sum).1
      ((w.map paperAxisCellLetterCoordinates).sum).2) :
    ∃ hv : NonnegativePrimitiveDirection
        (quadrantCoordinates k ((w.map paperAxisCellLetterCoordinates).sum)),
      IsConj ((w.map paperQuadrilateralSideNeighbor).prod)
        (quadrantPrimitiveTraceWord k ((w.map paperAxisCellLetterCoordinates).sum) hv)⁻¹ := by
  have hsum : ((quadrantLowerMechanicalSideWord k m n).map paperAxisCellLetterCoordinates).sum =
      -(w.map paperAxisCellLetterCoordinates).sum := by
    rw [← hWord, sideWord_opposite_sum, List.map_reverse, List.sum_reverse, sideWord_rotate_sum]
  have hc : quadrantCoordinates k ((w.map paperAxisCellLetterCoordinates).sum) =
      ((m : ℤ), (n : ℤ)) := by
    have h := quadrantLowerMechanicalSideWord_negative_sum_coordinates k m n hn
    rwa [hsum, neg_neg] at h
  obtain ⟨hv, hcan⟩ := mechanical_canonical_for_label k m n
    ((w.map paperAxisCellLetterCoordinates).sum) hp hc
  refine ⟨hv, ?_⟩
  have hprod : ((quadrantLowerMechanicalSideWord k m n).map paperQuadrilateralSideNeighbor).prod =
      (((w.rotate r).map paperQuadrilateralSideNeighbor).prod)⁻¹ := by
    rw [← hWord]
    exact sideWord_opposite_reverse_prod (w.rotate r)
  have hi := congrArg (fun x : modularTraceSubgroup => x⁻¹) (hprod.symm.trans hcan)
  simp only [inv_inv] at hi
  have h := sideWord_rotate_isConj w r
  rwa [hi] at h

end Markov
