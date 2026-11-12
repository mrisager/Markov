import Markov.FareyMechanicalWords
import Markov.SeededWordCoordinates
import Markov.PaperQuadrilateralRawSideFrame
import Mathlib.Data.List.Rotate

/-! The explicit lower mechanical lists evaluate to the EXISTING literal
canonical seeded matrix and actual subgroup words. The actual signed original
side alphabet and every cyclic rotation retain exact products/conjugators.
No geometric itinerary is asserted to have this normal form here. -/

namespace Markov
open scoped MatrixGroups

/-- Evaluate the explicitly quotient-defined binary word in any actual monoid. -/
def lowerMechanicalEval {G : Type*} [Monoid G] (x y : G) (p q : ℕ) : G :=
  ((lowerMechanicalWord p q).map (fun b => if b then y else x)).prod

theorem lowerMechanicalEval_map {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (x y : G) (p q : ℕ) :
    f (lowerMechanicalEval x y p q) = lowerMechanicalEval (f x) (f y) p q := by
  unfold lowerMechanicalEval
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  cases b <;> rfl

/-- The explicit words evaluate by the same ordered multiplication as the
actual Farey recursion, in every monoid. -/
theorem lowerMechanicalEval_farey_concat {G : Type*} [Monoid G]
    (x y : G) (a b c d : ℕ) (hd : a * d = b * c + 1) :
    lowerMechanicalEval x y (a + c) (b + d) =
      lowerMechanicalEval x y a b * lowerMechanicalEval x y c d := by
  unfold lowerMechanicalEval
  rw [lowerMechanicalWord_farey_concat a b c d hd, List.map_append, List.prod_append]

private theorem mechanical_nat_det (u v : ℤ × ℤ)
    (hu1 : 0 ≤ u.1) (hu2 : 0 ≤ u.2) (hv1 : 0 ≤ v.1) (hv2 : 0 ≤ v.2)
    (hd : intDet u v = 1) :
    u.1.toNat * v.2.toNat = u.2.toNat * v.1.toNat + 1 := by
  apply Int.ofNat_inj.mp
  push_cast
  rw [Int.toNat_of_nonneg hu1, Int.toNat_of_nonneg hv2,
    Int.toNat_of_nonneg hu2, Int.toNat_of_nonneg hv1]
  dsimp [intDet] at hd
  omega

/-- Every actual coordinate SeededFarey pair is evaluated by the explicit
quotient-defined words at its actual coordinate labels. No word witness or
word-class equivalence is assumed. -/
theorem SeededFarey.coordinate_lowerMechanicalEval
    {M0 N0 M N : IntMatrixTwo} {u v : ℤ × ℤ}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) :
    lowerMechanicalEval M0 N0 u.1.toNat u.2.toNat = M ∧
      lowerMechanicalEval M0 N0 v.1.toNat v.2.toNat = N := by
  induction h with
  | seed =>
    constructor <;>
      simp [lowerMechanicalEval, lowerMechanicalWord_seed_left, lowerMechanicalWord_seed_right]
  | @left u v M N hh ih =>
    have hn := hh.coordinate_nonnegative_labels
    have hd := mechanical_nat_det u v hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
      hh.coordinate_det_eq_one
    refine ⟨ih.1, ?_⟩
    simp only [Prod.fst_add, Prod.snd_add,
      Int.toNat_add hn.1 hn.2.2.1, Int.toNat_add hn.2.1 hn.2.2.2]
    rw [lowerMechanicalEval_farey_concat M0 N0 _ _ _ _ hd, ih.1, ih.2]
  | @right u v M N hh ih =>
    have hn := hh.coordinate_nonnegative_labels
    have hd := mechanical_nat_det u v hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
      hh.coordinate_det_eq_one
    refine ⟨?_, ih.2⟩
    simp only [Prod.fst_add, Prod.snd_add,
      Int.toNat_add hn.1 hn.2.2.1, Int.toNat_add hn.2.1 hn.2.2.2]
    rw [lowerMechanicalEval_farey_concat M0 N0 _ _ _ _ hd, ih.1, ih.2]

/-- Exact equality with the already defined canonical matrix: primitivity
selects a literal Farey witness, whose actual ordered word is computed above. -/
theorem primitiveSeedMatrix_eq_lowerMechanicalEval
    (M0 N0 : IntMatrixTwo) (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    primitiveSeedMatrix M0 N0 p hp = lowerMechanicalEval M0 N0 p.1.toNat p.2.toNat := by
  rcases primitiveSeedMatrix_spec M0 N0 p hp with ⟨v, N, h⟩ | ⟨u, M, h⟩
  · exact (h.primitiveSeedMatrix_left hp).trans h.coordinate_lowerMechanicalEval.1.symm
  · exact (h.primitiveSeedMatrix_right hp).trans h.coordinate_lowerMechanicalEval.2.symm

/-- The explicit signed original-side list for the actual quadrant seeds.
Its two letters are literally k and NextSide k, not an unspecified coding. -/
def quadrantLowerMechanicalSideWord (k : Fin 4) (p q : ℕ) : List (Fin 4) :=
  (lowerMechanicalWord p q).map (fun b => if b then paperQuadrilateralNextSide k else k)

private def mechanical_matrixHom : modularTraceSubgroup →* IntMatrixTwo where
  toFun g := (g.val : IntMatrixTwo)
  map_one' := rfl
  map_mul' g h := by
    change ((g.val * h.val : SL(2, ℤ)) : IntMatrixTwo) = _
    exact Matrix.SpecialLinearGroup.coe_mul g.val h.val

private theorem mechanical_quadrant_seed_matrices (k : Fin 4) :
    mechanical_matrixHom (paperQuadrilateralSideNeighbor k) = (quadrantSeedMatrices k).1 ∧
      mechanical_matrixHom (paperQuadrilateralSideNeighbor (paperQuadrilateralNextSide k)) =
        (quadrantSeedMatrices k).2 := by
  fin_cases k <;> constructor <;> decide

/-- The explicit signed side-word product is the EXISTING actual canonical
subgroup word, with literal equality rather than agreement of homology/traces. -/
theorem quadrantPrimitiveTraceWord_eq_lowerMechanicalSideWord_prod
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    quadrantPrimitiveTraceWord k p hp =
      ((quadrantLowerMechanicalSideWord k (quadrantCoordinates k p).1.toNat
        (quadrantCoordinates k p).2.toNat).map paperQuadrilateralSideNeighbor).prod := by
  have heval (a b : ℕ) :
      ((quadrantLowerMechanicalSideWord k a b).map paperQuadrilateralSideNeighbor).prod =
        lowerMechanicalEval (paperQuadrilateralSideNeighbor k)
          (paperQuadrilateralSideNeighbor (paperQuadrilateralNextSide k)) a b := by
    unfold quadrantLowerMechanicalSideWord lowerMechanicalEval
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    cases t <;> rfl
  apply Subtype.ext
  apply Subtype.ext
  change primitiveSeedMatrix (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
    (quadrantCoordinates k p) hp = mechanical_matrixHom _
  rw [heval, lowerMechanicalEval_map,
    (mechanical_quadrant_seed_matrices k).1, (mechanical_quadrant_seed_matrices k).2]
  exact primitiveSeedMatrix_eq_lowerMechanicalEval _ _ _ hp

private theorem mechanical_rotate_prod {G : Type*} [Group G] (w : List G) (r : ℕ) :
    (w.rotate r).prod = (w.take (r % w.length)).prod⁻¹ * w.prod *
      (w.take (r % w.length)).prod := by
  rw [List.rotate_eq_drop_append_take_mod, List.prod_append]
  have hs : w.prod = (w.take (r % w.length)).prod * (w.drop (r % w.length)).prod := by
    rw [← List.prod_append, List.take_append_drop]
  rw [hs]
  simp only [inv_mul_cancel_left]

/-- Every rotation of the signed mechanical list evaluates to the
canonical subgroup word up to conjugation by the explicit prefix. -/
theorem quadrantLowerMechanicalSideWord_rotate_prod
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) (r : ℕ) :
    (((quadrantLowerMechanicalSideWord k (quadrantCoordinates k p).1.toNat
        (quadrantCoordinates k p).2.toNat).rotate r).map paperQuadrilateralSideNeighbor).prod =
      (((quadrantLowerMechanicalSideWord k (quadrantCoordinates k p).1.toNat
          (quadrantCoordinates k p).2.toNat).take
            (r % (quadrantLowerMechanicalSideWord k (quadrantCoordinates k p).1.toNat
              (quadrantCoordinates k p).2.toNat).length)).map paperQuadrilateralSideNeighbor).prod⁻¹ *
        quadrantPrimitiveTraceWord k p hp *
      (((quadrantLowerMechanicalSideWord k (quadrantCoordinates k p).1.toNat
          (quadrantCoordinates k p).2.toNat).take
            (r % (quadrantLowerMechanicalSideWord k (quadrantCoordinates k p).1.toNat
              (quadrantCoordinates k p).2.toNat).length)).map paperQuadrilateralSideNeighbor).prod := by
  have h := mechanical_rotate_prod
    ((quadrantLowerMechanicalSideWord k (quadrantCoordinates k p).1.toNat
      (quadrantCoordinates k p).2.toNat).map paperQuadrilateralSideNeighbor) r
  rw [← List.map_rotate] at h
  simp only [List.length_map, ← List.map_take] at h
  rwa [← quadrantPrimitiveTraceWord_eq_lowerMechanicalSideWord_prod k p hp] at h

end Markov
