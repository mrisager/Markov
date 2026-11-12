import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic

/-! The exact positive-multiple decomposition of a nonzero integer pair
into a signed primitive pair. The multiplicity is the natural gcd of the
absolute coordinate values, so no sign quotient is introduced. -/

noncomputable section

namespace Markov

/-- A signed primitive direction in the full standard integer lattice. -/
abbrev PrimitiveIntegerRay := {k : ℤ × ℤ // IsCoprime k.1 k.2}

/-- The standard lattice with exactly its zero vector removed. -/
abbrev NonzeroIntegerDirection := {d : ℤ × ℤ // d ≠ (0, 0)}

theorem coprime_integerPair_ne_zero {k : ℤ × ℤ} (hk : IsCoprime k.1 k.2) :
    k ≠ (0, 0) := by
  intro hz
  apply not_isCoprime_zero_zero (R := ℤ)
  simpa only [hz] using hk

theorem integerPair_gcd_pos {d : ℤ × ℤ} (hd : d ≠ (0, 0)) :
    0 < Int.gcd d.1 d.2 := by
  apply Nat.pos_of_ne_zero
  intro hg
  exact hd (Prod.ext (Int.gcd_eq_zero_iff.mp hg).1 (Int.gcd_eq_zero_iff.mp hg).2)

/-- Multiplication of a signed primitive direction by a positive integer. -/
def primitiveRayCompose (p : ℕ+ × PrimitiveIntegerRay) : NonzeroIntegerDirection :=
  ⟨(((p.1 : ℕ) : ℤ) * p.2.1.1, ((p.1 : ℕ) : ℤ) * p.2.1.2), by
    intro hz
    have hm : ((p.1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast p.1.ne_zero
    apply coprime_integerPair_ne_zero p.2.2
    apply Prod.ext
    · exact (mul_eq_zero.mp (congrArg Prod.fst hz)).resolve_left hm
    · exact (mul_eq_zero.mp (congrArg Prod.snd hz)).resolve_left hm⟩

/-- The canonical primitive ray data, obtained by dividing both integer
coordinates by their positive natural gcd. -/
def primitiveRayDecompose (d : NonzeroIntegerDirection) : ℕ+ × PrimitiveIntegerRay :=
  (⟨Int.gcd d.1.1 d.1.2, integerPair_gcd_pos d.2⟩,
    ⟨(d.1.1 / (Int.gcd d.1.1 d.1.2 : ℤ), d.1.2 / (Int.gcd d.1.1 d.1.2 : ℤ)),
      Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_ediv_gcd_ediv_gcd (integerPair_gcd_pos d.2))⟩)

/-- Composing the gcd multiplicity and normalized coordinates recovers the original vector. -/
@[simp] theorem primitiveRayCompose_decompose (d : NonzeroIntegerDirection) :
    primitiveRayCompose (primitiveRayDecompose d) = d := by
  apply Subtype.ext
  apply Prod.ext
  · change (Int.gcd d.1.1 d.1.2 : ℤ) * (d.1.1 / (Int.gcd d.1.1 d.1.2 : ℤ)) = d.1.1
    rw [mul_comm, Int.ediv_mul_cancel (Int.gcd_dvd_left _ _)]
  · change (Int.gcd d.1.1 d.1.2 : ℤ) * (d.1.2 / (Int.gcd d.1.1 d.1.2 : ℤ)) = d.1.2
    rw [mul_comm, Int.ediv_mul_cancel (Int.gcd_dvd_right _ _)]

/-- The gcd of a positive multiple of a primitive pair is exactly the positive multiplier. -/
theorem primitiveRayCompose_gcd (p : ℕ+ × PrimitiveIntegerRay) :
    Int.gcd (primitiveRayCompose p).1.1 (primitiveRayCompose p).1.2 = (p.1 : ℕ) := by
  change Int.gcd (((p.1 : ℕ) : ℤ) * p.2.1.1) (((p.1 : ℕ) : ℤ) * p.2.1.2) = _
  rw [Int.gcd_mul_left, Int.natAbs_natCast, Int.isCoprime_iff_gcd_eq_one.mp p.2.2, mul_one]

/-- Normalizing a positive primitive multiple recovers both its multiplier and its signed ray. -/
@[simp] theorem primitiveRayDecompose_compose (p : ℕ+ × PrimitiveIntegerRay) :
    primitiveRayDecompose (primitiveRayCompose p) = p := by
  have hg := primitiveRayCompose_gcd p
  have hm : ((p.1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast p.1.ne_zero
  apply Prod.ext
  · apply Subtype.ext
    exact hg
  · apply Subtype.ext
    apply Prod.ext
    · change (((p.1 : ℕ) : ℤ) * p.2.1.1) /
        (Int.gcd (primitiveRayCompose p).1.1 (primitiveRayCompose p).1.2 : ℤ) = p.2.1.1
      rw [hg, Int.mul_ediv_cancel_left _ hm]
    · change (((p.1 : ℕ) : ℤ) * p.2.1.2) /
        (Int.gcd (primitiveRayCompose p).1.1 (primitiveRayCompose p).1.2 : ℤ) = p.2.1.2
      rw [hg, Int.mul_ediv_cancel_left _ hm]

/-- Nonzero integer vectors are in bijection with a positive integer and
a signed primitive direction, retaining both signs as distinct rays. -/
def primitiveRayEquiv : NonzeroIntegerDirection ≃ ℕ+ × PrimitiveIntegerRay where
  toFun := primitiveRayDecompose
  invFun := primitiveRayCompose
  left_inv := primitiveRayCompose_decompose
  right_inv := primitiveRayDecompose_compose

@[simp] theorem primitiveRayEquiv_apply (d : NonzeroIntegerDirection) :
    primitiveRayEquiv d = primitiveRayDecompose d := rfl

@[simp] theorem primitiveRayEquiv_symm_apply (p : ℕ+ × PrimitiveIntegerRay) :
    primitiveRayEquiv.symm p = primitiveRayCompose p := rfl

/-- The equivalence's inverse is exactly ordinary positive integer scalar multiplication. -/
theorem primitiveRayEquiv_symm_val (p : ℕ+ × PrimitiveIntegerRay) :
    (primitiveRayEquiv.symm p).1 = (p.1 : ℕ) • p.2.1 := by
  ext <;> simp [primitiveRayEquiv, primitiveRayCompose, nsmul_eq_mul]

/-- The forward map has the literal positive-gcd multiplicity. -/
theorem primitiveRayEquiv_multiplicity (d : NonzeroIntegerDirection) :
    ((primitiveRayEquiv d).1 : ℕ) = Int.gcd d.1.1 d.1.2 := rfl

/-- The canonical positive primitive factorization of a nonzero integer vector. -/
theorem primitiveRayEquiv_factorization (d : NonzeroIntegerDirection) :
    (((primitiveRayEquiv d).1 : ℕ) • (primitiveRayEquiv d).2.1) = d.1 := by
  rw [← primitiveRayEquiv_symm_val, Equiv.symm_apply_apply]

/-- The positive primitive factorization is unique as a multiplier-ray pair. -/
theorem exists_unique_positive_primitive_ray (d : ℤ × ℤ) (hd : d ≠ (0, 0)) :
    ∃! p : ℕ+ × PrimitiveIntegerRay, (p.1 : ℕ) • p.2.1 = d := by
  refine ⟨primitiveRayEquiv ⟨d, hd⟩, primitiveRayEquiv_factorization ⟨d, hd⟩, ?_⟩
  intro p hp
  apply primitiveRayEquiv.symm.injective
  apply Subtype.ext
  rw [primitiveRayEquiv_symm_val, hp, Equiv.symm_apply_apply]

end Markov
