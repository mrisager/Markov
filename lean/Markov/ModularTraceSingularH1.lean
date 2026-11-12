import Markov.SingularHurewiczInverse
import Markov.ModularMarkedLoops

/-! Actual integral singular H1 of the constructed modular orbit quotient,
with the original positive paper-generator marking. Actual orbit representatives
and actual upper-half-plane paths supply every connector. No homology or
Hurewicz assumption, surface classification or simple-curve claim is used.
The equivalence is indexed by the chosen lift z; transport of loops based
elsewhere to a fixed-z marking is not proved or assumed in this file. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- An actual upper-half-plane representative of each actual quotient point. -/
def modularTraceSingularRepresentative (q : ModularTraceQuotient) : UpperHalfPlane :=
  Classical.choose (modularTraceQuotientMk_surjective q)

theorem modularTraceSingularRepresentative_spec (q : ModularTraceQuotient) :
    modularTraceQuotientMk (modularTraceSingularRepresentative q) = q :=
  Classical.choose_spec (modularTraceQuotientMk_surjective q)

/-- Actual connecting paths in the actual quotient, obtained by projecting
actual upper-half-plane paths to the chosen actual orbit representatives. -/
def modularTraceSingularConnector (z : UpperHalfPlane) (q : ModularTraceQuotient) :
    Path (modularTraceQuotientMk z) q :=
  ((PathConnectedSpace.somePath z (modularTraceSingularRepresentative q)).map
    modularTraceQuotientMk_continuous).cast rfl (modularTraceSingularRepresentative_spec q).symm

/-- The already proved original-marked algebraic abelianization equivalence
in additive notation, kept separate from actual singular homology. -/
def modularTraceMarkedAbelianizationAddEquiv (z : UpperHalfPlane) :
    BasedLoopAbelianGroup ModularTraceQuotient (modularTraceQuotientMk z) ≃+ (ℤ × ℤ) :=
  (modularTraceMarkedAbelianizationEquiv z).toAdditiveLeft

/-- The actual integral singular H1 group is Z², through the proved genuine
Hurewicz equivalence and actual connectors, with no conditional H1 premise. -/
def modularTraceSingularH1Equiv (z : UpperHalfPlane) :
    integralSingularH1 ModularTraceQuotient ≃+ (ℤ × ℤ) :=
  (singularHurewiczAddEquiv ModularTraceQuotient (modularTraceQuotientMk z)
    (modularTraceSingularConnector z)).symm.trans (modularTraceMarkedAbelianizationAddEquiv z)

/-- Exact normalization on each actual oriented based loop. -/
theorem modularTraceSingularH1Equiv_loop (z : UpperHalfPlane)
    (γ : Path (modularTraceQuotientMk z) (modularTraceQuotientMk z)) :
    modularTraceSingularH1Equiv z (singularLoopClass ModularTraceQuotient γ) =
      (modularTraceMarkedCoordinates z (FundamentalGroup.fromPath (.mk γ))).toAdd := by
  change modularTraceMarkedAbelianizationAddEquiv z
    ((singularHurewiczAddEquiv ModularTraceQuotient (modularTraceQuotientMk z)
      (modularTraceSingularConnector z)).symm (singularLoopClass ModularTraceQuotient γ)) = _
  rw [← singularHurewiczAddEquiv_loop ModularTraceQuotient (modularTraceQuotientMk z)
    (modularTraceSingularConnector z) γ, AddEquiv.symm_apply_apply]
  rfl

/-- Every actual forward deck loop has its literal original-paper
abelianization coordinates as an actual singular homology class. -/
theorem modularTraceSingularH1Equiv_forwardLoop (z : UpperHalfPlane) (g : modularTraceSubgroup) :
    modularTraceSingularH1Equiv z
      (singularLoopClass ModularTraceQuotient (modularTraceForwardLoop z g)) =
        (paperTraceAbelianizationCoordinates g).toAdd := by
  rw [modularTraceSingularH1Equiv_loop, modularTraceMarkedCoordinates_forwardLoop]

@[simp] theorem modularTraceSingularH1Equiv_basis_zero (z : UpperHalfPlane) :
    modularTraceSingularH1Equiv z (singularLoopClass ModularTraceQuotient
      (modularTraceForwardLoop z (paperTraceFreeGroupBasis 0))) = ((1, 0) : ℤ × ℤ) := by
  rw [modularTraceSingularH1Equiv_forwardLoop, paperTraceAbelianizationCoordinates_basis_zero]
  rfl

@[simp] theorem modularTraceSingularH1Equiv_basis_one (z : UpperHalfPlane) :
    modularTraceSingularH1Equiv z (singularLoopClass ModularTraceQuotient
      (modularTraceForwardLoop z (paperTraceFreeGroupBasis 1))) = ((0, 1) : ℤ × ℤ) := by
  rw [modularTraceSingularH1Equiv_forwardLoop, paperTraceAbelianizationCoordinates_basis_one]
  rfl

/-- The literal positive original paper matrix A gives the first positive
standard generator of actual integral singular H1. -/
theorem modularTraceSingularH1Equiv_generatorA (z : UpperHalfPlane) :
    modularTraceSingularH1Equiv z (singularLoopClass ModularTraceQuotient
      (modularTraceForwardLoop z (⟨paperGeneratorASL, by
        rw [← paperTraceSubgroup_eq_modularTraceSubgroup]
        exact paperGeneratorASL_mem_paperTraceSubgroup⟩ : modularTraceSubgroup))) =
      ((1, 0) : ℤ × ℤ) := by
  have he : (⟨paperGeneratorASL, by
        rw [← paperTraceSubgroup_eq_modularTraceSubgroup]
        exact paperGeneratorASL_mem_paperTraceSubgroup⟩ : modularTraceSubgroup) =
      paperTraceFreeGroupBasis 0 := Subtype.ext paperTraceFreeGroupBasis_zero.symm
  rw [he]
  exact modularTraceSingularH1Equiv_basis_zero z

/-- The literal positive original paper matrix B gives the second positive
standard generator, with no reversal or coordinate interchange. -/
theorem modularTraceSingularH1Equiv_generatorB (z : UpperHalfPlane) :
    modularTraceSingularH1Equiv z (singularLoopClass ModularTraceQuotient
      (modularTraceForwardLoop z (⟨paperGeneratorBSL, by
        rw [← paperTraceSubgroup_eq_modularTraceSubgroup]
        exact paperGeneratorBSL_mem_paperTraceSubgroup⟩ : modularTraceSubgroup))) =
      ((0, 1) : ℤ × ℤ) := by
  have he : (⟨paperGeneratorBSL, by
        rw [← paperTraceSubgroup_eq_modularTraceSubgroup]
        exact paperGeneratorBSL_mem_paperTraceSubgroup⟩ : modularTraceSubgroup) =
      paperTraceFreeGroupBasis 1 := Subtype.ext paperTraceFreeGroupBasis_one.symm
  rw [he]
  exact modularTraceSingularH1Equiv_basis_one z

end Markov
