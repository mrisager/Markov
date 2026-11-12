import Markov.PaperFreeGroup
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! The algebraic abelianization of the actual modular trace subgroup,
with the original paper-generator marking. This does not assert singular
homology, a Hurewicz identification, or any surface classification. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

private def finTwoFinsuppIntPair : (Fin 2 →₀ ℤ) ≃+ (ℤ × ℤ) where
  toFun f := (f 0, f 1)
  invFun z := Finsupp.single 0 z.1 + Finsupp.single 1 z.2
  left_inv f := by
    ext i
    fin_cases i <;> simp
  right_inv z := by
    ext <;> simp
  map_add' f g := rfl

private def freeTwoAbelianizationCoordinates :
    Abelianization (FreeGroup (Fin 2)) ≃* Multiplicative (ℤ × ℤ) :=
  ((FreeAbelianGroup.equivFinsupp (Fin 2)).trans finTwoFinsuppIntPair).toMultiplicativeRight

private theorem freeTwoAbelianizationCoordinates_of (i : Fin 2) :
    freeTwoAbelianizationCoordinates (Abelianization.of (FreeGroup.of i)) =
      Multiplicative.ofAdd ((Finsupp.single i (1 : ℤ)) 0,
        (Finsupp.single i (1 : ℤ)) 1) := by
  change Multiplicative.ofAdd (finTwoFinsuppIntPair
    (FreeAbelianGroup.equivFinsupp (Fin 2) (FreeAbelianGroup.of i))) = _
  simp [FreeAbelianGroup.equivFinsupp, finTwoFinsuppIntPair]

/-- The genuine algebraic abelianization of the actual generated subgroup
is the standard rank-two integer lattice in the original paper marking. -/
def paperTraceAbelianizationEquiv :
    Abelianization modularTraceSubgroup ≃* Multiplicative (ℤ × ℤ) :=
  paperTraceFreeGroupBasis.repr.abelianizationCongr.trans freeTwoAbelianizationCoordinates

/-- The first actual paper free generator has coordinate `(1,0)`. -/
@[simp] theorem paperTraceAbelianizationEquiv_basis_zero :
    paperTraceAbelianizationEquiv (Abelianization.of (paperTraceFreeGroupBasis 0)) =
      Multiplicative.ofAdd ((1, 0) : ℤ × ℤ) := by
  change freeTwoAbelianizationCoordinates
    (Abelianization.of (paperTraceFreeGroupBasis.repr (paperTraceFreeGroupBasis 0))) = _
  rw [FreeGroupBasis.repr_apply_coe, freeTwoAbelianizationCoordinates_of]
  norm_num

/-- The second actual paper free generator has coordinate `(0,1)`. -/
@[simp] theorem paperTraceAbelianizationEquiv_basis_one :
    paperTraceAbelianizationEquiv (Abelianization.of (paperTraceFreeGroupBasis 1)) =
      Multiplicative.ofAdd ((0, 1) : ℤ × ℤ) := by
  change freeTwoAbelianizationCoordinates
    (Abelianization.of (paperTraceFreeGroupBasis.repr (paperTraceFreeGroupBasis 1))) = _
  rw [FreeGroupBasis.repr_apply_coe, freeTwoAbelianizationCoordinates_of]
  norm_num

/-- The literal original paper matrix A, as an element of the actual
subgroup, has the positive first standard abelianization coordinate. -/
theorem paperTraceAbelianizationEquiv_generatorA :
    paperTraceAbelianizationEquiv (Abelianization.of
      (⟨paperGeneratorASL, by
        rw [← paperTraceSubgroup_eq_modularTraceSubgroup]
        exact paperGeneratorASL_mem_paperTraceSubgroup⟩ : modularTraceSubgroup)) =
      Multiplicative.ofAdd ((1, 0) : ℤ × ℤ) := by
  have he : (⟨paperGeneratorASL, by
        rw [← paperTraceSubgroup_eq_modularTraceSubgroup]
        exact paperGeneratorASL_mem_paperTraceSubgroup⟩ : modularTraceSubgroup) =
      paperTraceFreeGroupBasis 0 := Subtype.ext paperTraceFreeGroupBasis_zero.symm
  rw [he]
  exact paperTraceAbelianizationEquiv_basis_zero

/-- The literal original paper matrix B has the positive second standard
coordinate, with the original order and signs preserved. -/
theorem paperTraceAbelianizationEquiv_generatorB :
    paperTraceAbelianizationEquiv (Abelianization.of
      (⟨paperGeneratorBSL, by
        rw [← paperTraceSubgroup_eq_modularTraceSubgroup]
        exact paperGeneratorBSL_mem_paperTraceSubgroup⟩ : modularTraceSubgroup)) =
      Multiplicative.ofAdd ((0, 1) : ℤ × ℤ) := by
  have he : (⟨paperGeneratorBSL, by
        rw [← paperTraceSubgroup_eq_modularTraceSubgroup]
        exact paperGeneratorBSL_mem_paperTraceSubgroup⟩ : modularTraceSubgroup) =
      paperTraceFreeGroupBasis 1 := Subtype.ext paperTraceFreeGroupBasis_one.symm
  rw [he]
  exact paperTraceAbelianizationEquiv_basis_one

/-- The canonical integer-coordinate homomorphism is obtained from actual
algebraic abelianization, rather than an assumed topological marking. -/
def paperTraceAbelianizationCoordinates : modularTraceSubgroup →* Multiplicative (ℤ × ℤ) :=
  paperTraceAbelianizationEquiv.toMonoidHom.comp Abelianization.of

@[simp] theorem paperTraceAbelianizationCoordinates_basis_zero :
    paperTraceAbelianizationCoordinates (paperTraceFreeGroupBasis 0) =
      Multiplicative.ofAdd ((1, 0) : ℤ × ℤ) :=
  paperTraceAbelianizationEquiv_basis_zero

@[simp] theorem paperTraceAbelianizationCoordinates_basis_one :
    paperTraceAbelianizationCoordinates (paperTraceFreeGroupBasis 1) =
      Multiplicative.ofAdd ((0, 1) : ℤ × ℤ) :=
  paperTraceAbelianizationEquiv_basis_one

end Markov
