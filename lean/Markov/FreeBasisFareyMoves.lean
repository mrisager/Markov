import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.Tactic

/-! Explicit invertible Nielsen substitutions for a two-element free basis.
The Farey left/right products remain an actual free basis, proved through
mutually inverse lifted substitutions. No Hopfian or geometric input is used. -/

noncomputable section
namespace Markov

variable {G : Type*} [Group G]

private theorem basis_lift_apply (b : FreeGroupBasis (Fin 2) G) (f : Fin 2 → G)
    (i : Fin 2) : b.lift f (b i) = f i := by
  change FreeGroup.lift f (b.repr (b i)) = f i
  rw [FreeGroupBasis.repr_apply_coe, FreeGroup.lift_apply_of]

/-- The actual Nielsen automorphism sending `(a,b)` to `(a,a*b)`.
The inverse substitution fixes `a` and sends `b` to `a⁻¹*b`. -/
def freeBasisFareyLeftAutomorphism (b : FreeGroupBasis (Fin 2) G) : G ≃* G :=
  let f : G →* G := b.lift ![b 0, b 0 * b 1]
  let g : G →* G := b.lift ![b 0, (b 0)⁻¹ * b 1]
  MonoidHom.toMulEquiv f g
    (by
      apply b.ext_hom
      intro i
      fin_cases i <;> simp [f, g])
    (by
      apply b.ext_hom
      intro i
      fin_cases i <;> simp [f, g])

/-- The actual Nielsen automorphism sending `(a,b)` to `(a*b,b)`.
The inverse substitution sends `a` to `a*b⁻¹` and fixes `b`. -/
def freeBasisFareyRightAutomorphism (b : FreeGroupBasis (Fin 2) G) : G ≃* G :=
  let f : G →* G := b.lift ![b 0 * b 1, b 1]
  let g : G →* G := b.lift ![b 0 * (b 1)⁻¹, b 1]
  MonoidHom.toMulEquiv f g
    (by
      apply b.ext_hom
      intro i
      fin_cases i <;> simp [f, g, mul_assoc])
    (by
      apply b.ext_hom
      intro i
      fin_cases i <;> simp [f, g, mul_assoc])

/-- The Farey left move preserves an actual two-element free basis. -/
def freeBasisFareyLeft (b : FreeGroupBasis (Fin 2) G) : FreeGroupBasis (Fin 2) G :=
  b.map (freeBasisFareyLeftAutomorphism b)

/-- The Farey right move preserves an actual two-element free basis. -/
def freeBasisFareyRight (b : FreeGroupBasis (Fin 2) G) : FreeGroupBasis (Fin 2) G :=
  b.map (freeBasisFareyRightAutomorphism b)

@[simp] theorem freeBasisFareyLeft_zero (b : FreeGroupBasis (Fin 2) G) :
    freeBasisFareyLeft b 0 = b 0 := by
  change b.lift ![b 0, b 0 * b 1] (b 0) = b 0
  rw [basis_lift_apply]
  rfl

@[simp] theorem freeBasisFareyLeft_one (b : FreeGroupBasis (Fin 2) G) :
    freeBasisFareyLeft b 1 = b 0 * b 1 := by
  change b.lift ![b 0, b 0 * b 1] (b 1) = b 0 * b 1
  rw [basis_lift_apply]
  rfl

@[simp] theorem freeBasisFareyRight_zero (b : FreeGroupBasis (Fin 2) G) :
    freeBasisFareyRight b 0 = b 0 * b 1 := by
  change b.lift ![b 0 * b 1, b 1] (b 0) = b 0 * b 1
  rw [basis_lift_apply]
  rfl

@[simp] theorem freeBasisFareyRight_one (b : FreeGroupBasis (Fin 2) G) :
    freeBasisFareyRight b 1 = b 1 := by
  change b.lift ![b 0 * b 1, b 1] (b 1) = b 1
  rw [basis_lift_apply]
  rfl


private def freeBasisInvertAtAutomorphism (b : FreeGroupBasis (Fin 2) G) (j : Fin 2) : G ≃* G :=
  let f : G →* G := b.lift (fun i => if i = j then (b i)⁻¹ else b i)
  MonoidHom.toMulEquiv f f
    (by
      apply b.ext_hom
      intro i
      by_cases hij : i = j <;> simp [f, hij])
    (by
      apply b.ext_hom
      intro i
      by_cases hij : i = j <;> simp [f, hij])

/-- Inverting either specified generator preserves a genuine free basis. -/
def freeBasisInvertAt (b : FreeGroupBasis (Fin 2) G) (j : Fin 2) :
    FreeGroupBasis (Fin 2) G :=
  b.map (freeBasisInvertAtAutomorphism b j)

@[simp] theorem freeBasisInvertAt_apply (b : FreeGroupBasis (Fin 2) G) (j i : Fin 2) :
    freeBasisInvertAt b j i = if i = j then (b i)⁻¹ else b i := by
  change b.lift (fun k => if k = j then (b k)⁻¹ else b k) (b i) = _
  exact basis_lift_apply b _ i

/-- Swapping the two specified generators preserves their actual free basis. -/
def freeBasisSwap (b : FreeGroupBasis (Fin 2) G) : FreeGroupBasis (Fin 2) G :=
  b.reindex (Equiv.swap 0 1)

@[simp] theorem freeBasisSwap_zero (b : FreeGroupBasis (Fin 2) G) :
    freeBasisSwap b 0 = b 1 := by
  simp [freeBasisSwap, FreeGroupBasis.reindex_apply]

@[simp] theorem freeBasisSwap_one (b : FreeGroupBasis (Fin 2) G) :
    freeBasisSwap b 1 = b 0 := by
  simp [freeBasisSwap, FreeGroupBasis.reindex_apply]

end Markov
