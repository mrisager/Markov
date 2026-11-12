import Markov.PaperCuspHolonomy
import Markov.PrimitiveHolonomyNoProperPower
import Markov.ModularH1Transport
import Mathlib.Algebra.Group.Conj

/-! Literal essential-class obstructions for the actual canonical holonomies.
The cusp element is exactly the original generator commutator already proved
in SL(2,Z), now retained in the actual deck subgroup. Nonconjugacy is explicitly
inside that deck group. No geometric definition or classification of peripheral
curves is introduced. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- The literal checked original-generator commutator as an actual deck element. -/
def paperCuspDeckElement : modularTraceSubgroup :=
  ⟨paperCuspHolonomy,paperCuspHolonomy_mem_modularTraceSubgroup⟩

/-- This deck element is exactly the commutator of the original marked generators. -/
theorem paperCuspDeckElement_eq_original_commutator :
    paperCuspDeckElement = ⁅paperTraceFreeGroupBasis 0,paperTraceFreeGroupBasis 1⁆ := by
  apply Subtype.ext
  change paperCuspHolonomy =
    (paperTraceFreeGroupBasis 0 : SL(2, ℤ)) * (paperTraceFreeGroupBasis 1 : SL(2, ℤ)) *
      (paperTraceFreeGroupBasis 0 : SL(2, ℤ))⁻¹ * (paperTraceFreeGroupBasis 1 : SL(2, ℤ))⁻¹
  rw [paperTraceFreeGroupBasis_zero,paperTraceFreeGroupBasis_one]
  rfl

/-- The actual original abelianization sends the literal cusp commutator to zero. -/
theorem paperCuspDeckElement_coordinates :
    paperTraceAbelianizationCoordinates paperCuspDeckElement = 1 := by
  rw [paperCuspDeckElement_eq_original_commutator,map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)

/-- Every actual deck conjugate of every integer cusp power has zero original coordinates. -/
theorem paperCuspDeckElement_conjugate_zpow_coordinates (h : modularTraceSubgroup) (n : ℤ) :
    paperTraceAbelianizationCoordinates (h*paperCuspDeckElement^n*h⁻¹) = 1 := by
  rw [map_mul,map_mul,map_inv,map_zpow,paperCuspDeckElement_coordinates]
  simp

/-- Canonical primitive data have a nonzero literal signed integer label. -/
theorem paperPrimitiveDirection_ne_zero (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) : p≠0 := by
  intro he
  have hc := (quadrantCoordinates_coprime_iff k p).mp hp.2.2
  rw [he] at hc
  exact not_isCoprime_zero_zero hc

/-- The actual canonical holonomy is nontrivial in the actual deck group. -/
theorem paperPrimitiveHolonomy_ne_one (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) : paperPrimitiveHolonomy k p hp≠1 := by
  intro he
  have hc := congrArg paperTraceAbelianizationCoordinates he
  rw [paperPrimitiveHolonomy_coordinates,map_one] at hc
  exact paperPrimitiveDirection_ne_zero k p hp (congrArg Multiplicative.toAdd hc)

/-- The canonical holonomy is never any literal deck conjugate of an integer
power of the actual original-generator commutator. -/
theorem paperPrimitiveHolonomy_ne_conjugate_cusp_zpow (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p))
    (h : modularTraceSubgroup) (n : ℤ) :
    paperPrimitiveHolonomy k p hp ≠ h*paperCuspDeckElement^n*h⁻¹ := by
  intro he
  have hc := congrArg paperTraceAbelianizationCoordinates he
  rw [paperPrimitiveHolonomy_coordinates,paperCuspDeckElement_conjugate_zpow_coordinates] at hc
  exact paperPrimitiveDirection_ne_zero k p hp (congrArg Multiplicative.toAdd hc)

/-- The same literal exclusion in the actual group-theoretic IsConj relation. -/
theorem paperPrimitiveHolonomy_not_isConj_cusp_zpow (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) (n : ℤ) :
    ¬IsConj (paperPrimitiveHolonomy k p hp) (paperCuspDeckElement^n) := by
  intro he
  obtain ⟨h,hh⟩ := isConj_iff.mp he.symm
  exact paperPrimitiveHolonomy_ne_conjugate_cusp_zpow k p hp h n hh.symm

/-- The actual forward canonical period loop has nonzero genuine singular-H1 class. -/
theorem paperPrimitiveClosedGeodesicLoop_singularClass_ne_zero (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    singularLoopClass ModularTraceQuotient
      (modularClosedGeodesicLoop (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp)) ≠ 0 := by
  intro he
  have hc := congrArg modularTraceFixedSingularH1Equiv he
  rw [paperPrimitiveClosedGeodesicLoop_fixedSingularCoordinates,map_zero] at hc
  exact paperPrimitiveDirection_ne_zero k p hp hc

/-- The actual forward canonical period loop is not based path homotopic to refl. -/
theorem paperPrimitiveClosedGeodesicLoop_not_homotopic_refl (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    ¬(modularClosedGeodesicLoop (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp)).Homotopic
      (Path.refl (modularClosedGeodesic (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp) 0)) := by
  rintro ⟨H⟩
  apply paperPrimitiveClosedGeodesicLoop_singularClass_ne_zero k p hp
  have he := singularLoopClass_homotopy ModularTraceQuotient H
  simpa only [singularLoopClass_refl] using he

end Markov
