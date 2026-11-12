import Markov.ModularTraceFundamentalGroup
import Markov.PaperAbelianization

/-! The original forward paper-generator loops in the actual quotient.
The existing fundamental-group equivalence uses inverse endpoint labels.
Composing it with the proved restricted S-conjugation gives a marked
equivalence sending the forward A and B loops to A and B. This does not
identify singular homology or classify simple closed curves. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- Restriction of the actual S-conjugation to the actual trace subgroup. -/
def modularTraceSeedConjugation : modularTraceSubgroup ≃* modularTraceSubgroup :=
  (paperSeedConjugation.subgroupMap modularTraceSubgroup).trans
    (MulEquiv.subgroupCongr (by
      simpa only [paperTraceSubgroup_eq_modularTraceSubgroup] using
        paperTraceSubgroup_map_conjugation))

@[simp] theorem modularTraceSeedConjugation_coe (g : modularTraceSubgroup) :
    (modularTraceSeedConjugation g : SL(2, ℤ)) = paperSeedConjugation g.val := rfl

@[simp] theorem modularTraceSeedConjugation_basis (i : Fin 2) :
    modularTraceSeedConjugation (paperTraceFreeGroupBasis i) =
      (paperTraceFreeGroupBasis i)⁻¹ := by
  apply Subtype.ext
  change paperSeedConjugation (paperTraceFreeGroupBasis i : SL(2, ℤ)) =
    (paperTraceFreeGroupBasis i : SL(2, ℤ))⁻¹
  fin_cases i
  · change paperSeedConjugation (paperTraceFreeGroupBasis 0 : SL(2, ℤ)) =
      (paperTraceFreeGroupBasis 0 : SL(2, ℤ))⁻¹
    rw [paperTraceFreeGroupBasis_zero, paperSeedConjugation_paperA,
      modularGeneratorASL_eq_paperGeneratorASL_inv]
  · change paperSeedConjugation (paperTraceFreeGroupBasis 1 : SL(2, ℤ)) =
      (paperTraceFreeGroupBasis 1 : SL(2, ℤ))⁻¹
    rw [paperTraceFreeGroupBasis_one, paperSeedConjugation_paperB,
      modularGeneratorBSL_eq_paperGeneratorBSL_inv]

@[simp] theorem modularTraceSeedConjugation_inv_basis (i : Fin 2) :
    modularTraceSeedConjugation (paperTraceFreeGroupBasis i)⁻¹ =
      paperTraceFreeGroupBasis i := by
  rw [map_inv, modularTraceSeedConjugation_basis, inv_inv]

/-- The actual projection of a path from z to the forward endpoint g • z. -/
def modularTraceForwardLoop (z : UpperHalfPlane) (g : modularTraceSubgroup) :
    Path (modularTraceQuotientMk z) (modularTraceQuotientMk z) :=
  ((PathConnectedSpace.somePath z (g • z)).map modularTraceQuotientMk_continuous).cast
    rfl (modularTraceQuotientMk_smul g z).symm

theorem modularTraceForwardLoop_eq_deckLoop (z : UpperHalfPlane)
    (g : modularTraceSubgroup) :
    modularTraceForwardLoop z g = modularTraceDeckLoop z g⁻¹ := by
  ext t
  change modularTraceQuotientMk (PathConnectedSpace.somePath z (g • z) t) =
    modularTraceQuotientMk (PathConnectedSpace.somePath z (g⁻¹⁻¹ • z) t)
  rw [inv_inv]

@[simp] theorem modularTraceForwardLoop_apply (z : UpperHalfPlane)
    (g : modularTraceSubgroup) (t : unitInterval) :
    modularTraceForwardLoop z g t =
      modularTraceQuotientMk (PathConnectedSpace.somePath z (g • z) t) := rfl

/-- This composition corrects the labels of the original forward A/B
loops; it is not an assertion that every forward endpoint g is labelled g. -/
def modularTraceMarkedFundamentalGroupEquiv (z : UpperHalfPlane) :
    FundamentalGroup ModularTraceQuotient (modularTraceQuotientMk z) ≃*
      modularTraceSubgroup :=
  (modularTraceFundamentalGroupEquiv z).trans modularTraceSeedConjugation

theorem modularTraceMarkedFundamentalGroupEquiv_forwardLoop (z : UpperHalfPlane)
    (g : modularTraceSubgroup) :
    modularTraceMarkedFundamentalGroupEquiv z
      (FundamentalGroup.fromPath (.mk (modularTraceForwardLoop z g))) =
      modularTraceSeedConjugation g⁻¹ := by
  change modularTraceSeedConjugation (modularTraceFundamentalGroupEquiv z _) = _
  rw [modularTraceForwardLoop_eq_deckLoop, modularTraceFundamentalGroupEquiv_deckLoop]

@[simp] theorem modularTraceMarkedFundamentalGroupEquiv_forward_basis (z : UpperHalfPlane)
    (i : Fin 2) :
    modularTraceMarkedFundamentalGroupEquiv z
      (FundamentalGroup.fromPath (.mk (modularTraceForwardLoop z (paperTraceFreeGroupBasis i)))) =
      paperTraceFreeGroupBasis i := by
  rw [modularTraceMarkedFundamentalGroupEquiv_forwardLoop,
    modularTraceSeedConjugation_inv_basis]

/-- A genuine free basis of the actual quotient fundamental group with
the original forward paper-generator representatives. -/
def modularTraceMarkedFundamentalGroupBasis (z : UpperHalfPlane) :
    FreeGroupBasis (Fin 2)
      (FundamentalGroup ModularTraceQuotient (modularTraceQuotientMk z)) :=
  ⟨(modularTraceMarkedFundamentalGroupEquiv z).trans paperTraceFreeGroupEquiv.symm⟩

@[simp] theorem modularTraceMarkedFundamentalGroupBasis_generator (z : UpperHalfPlane)
    (i : Fin 2) :
    modularTraceMarkedFundamentalGroupBasis z i =
      FundamentalGroup.fromPath (.mk (modularTraceForwardLoop z (paperTraceFreeGroupBasis i))) := by
  apply (modularTraceMarkedFundamentalGroupEquiv z).injective
  rw [modularTraceMarkedFundamentalGroupEquiv_forward_basis]
  change (modularTraceMarkedFundamentalGroupEquiv z)
    ((modularTraceMarkedFundamentalGroupEquiv z).symm (paperTraceFreeGroupBasis i)) =
      paperTraceFreeGroupBasis i
  exact (modularTraceMarkedFundamentalGroupEquiv z).apply_symm_apply _

@[simp] theorem modularTraceMarkedFundamentalGroupEquiv_forward_zero (z : UpperHalfPlane) :
    ((modularTraceMarkedFundamentalGroupEquiv z
      (FundamentalGroup.fromPath (.mk (modularTraceForwardLoop z (paperTraceFreeGroupBasis 0)))) :
        modularTraceSubgroup) : SL(2, ℤ)) = paperGeneratorASL := by
  rw [modularTraceMarkedFundamentalGroupEquiv_forward_basis, paperTraceFreeGroupBasis_zero]

@[simp] theorem modularTraceMarkedFundamentalGroupEquiv_forward_one (z : UpperHalfPlane) :
    ((modularTraceMarkedFundamentalGroupEquiv z
      (FundamentalGroup.fromPath (.mk (modularTraceForwardLoop z (paperTraceFreeGroupBasis 1)))) :
        modularTraceSubgroup) : SL(2, ℤ)) = paperGeneratorBSL := by
  rw [modularTraceMarkedFundamentalGroupEquiv_forward_basis, paperTraceFreeGroupBasis_one]

theorem modularTraceForwardLoop_zero_apply (z : UpperHalfPlane) (t : unitInterval) :
    modularTraceForwardLoop z (paperTraceFreeGroupBasis 0) t =
      modularTraceQuotientMk (PathConnectedSpace.somePath z (paperGeneratorASL • z) t) := by
  change modularTraceQuotientMk
    (PathConnectedSpace.somePath z ((paperTraceFreeGroupBasis 0 : SL(2, ℤ)) • z) t) = _
  rw [paperTraceFreeGroupBasis_zero]

theorem modularTraceForwardLoop_one_apply (z : UpperHalfPlane) (t : unitInterval) :
    modularTraceForwardLoop z (paperTraceFreeGroupBasis 1) t =
      modularTraceQuotientMk (PathConnectedSpace.somePath z (paperGeneratorBSL • z) t) := by
  change modularTraceQuotientMk
    (PathConnectedSpace.somePath z ((paperTraceFreeGroupBasis 1 : SL(2, ℤ)) • z) t) = _
  rw [paperTraceFreeGroupBasis_one]

/-- S-conjugation negates both algebraic abelianization coordinates. -/
theorem paperTraceAbelianizationCoordinates_seedConjugation (g : modularTraceSubgroup) :
    paperTraceAbelianizationCoordinates (modularTraceSeedConjugation g) =
      (paperTraceAbelianizationCoordinates g)⁻¹ := by
  have hh : paperTraceAbelianizationCoordinates.comp modularTraceSeedConjugation.toMonoidHom =
      paperTraceAbelianizationCoordinates⁻¹ := by
    apply paperTraceFreeGroupBasis.ext_hom
    intro i
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      modularTraceSeedConjugation_basis, map_inv, MonoidHom.inv_apply]
  exact DFunLike.congr_fun hh g

/-- Algebraic abelianization coordinates for the explicitly marked
fundamental group. No singular-H1 identification is asserted. -/
def modularTraceMarkedCoordinates (z : UpperHalfPlane) :
    FundamentalGroup ModularTraceQuotient (modularTraceQuotientMk z) →*
      Multiplicative (ℤ × ℤ) :=
  paperTraceAbelianizationCoordinates.comp
    (modularTraceMarkedFundamentalGroupEquiv z).toMonoidHom

theorem modularTraceMarkedCoordinates_forwardLoop (z : UpperHalfPlane)
    (g : modularTraceSubgroup) :
    modularTraceMarkedCoordinates z
      (FundamentalGroup.fromPath (.mk (modularTraceForwardLoop z g))) =
      paperTraceAbelianizationCoordinates g := by
  change paperTraceAbelianizationCoordinates
    (modularTraceMarkedFundamentalGroupEquiv z _) = _
  rw [modularTraceMarkedFundamentalGroupEquiv_forwardLoop,
    paperTraceAbelianizationCoordinates_seedConjugation, map_inv, inv_inv]

@[simp] theorem modularTraceMarkedCoordinates_basis_zero (z : UpperHalfPlane) :
    modularTraceMarkedCoordinates z (modularTraceMarkedFundamentalGroupBasis z 0) =
      Multiplicative.ofAdd ((1, 0) : ℤ × ℤ) := by
  rw [modularTraceMarkedFundamentalGroupBasis_generator,
    modularTraceMarkedCoordinates_forwardLoop, paperTraceAbelianizationCoordinates_basis_zero]

@[simp] theorem modularTraceMarkedCoordinates_basis_one (z : UpperHalfPlane) :
    modularTraceMarkedCoordinates z (modularTraceMarkedFundamentalGroupBasis z 1) =
      Multiplicative.ofAdd ((0, 1) : ℤ × ℤ) := by
  rw [modularTraceMarkedFundamentalGroupBasis_generator,
    modularTraceMarkedCoordinates_forwardLoop, paperTraceAbelianizationCoordinates_basis_one]

def modularTraceMarkedAbelianizationEquiv (z : UpperHalfPlane) :
    Abelianization (FundamentalGroup ModularTraceQuotient (modularTraceQuotientMk z)) ≃*
      Multiplicative (ℤ × ℤ) :=
  (modularTraceMarkedFundamentalGroupEquiv z).abelianizationCongr.trans
    paperTraceAbelianizationEquiv

@[simp] theorem modularTraceMarkedAbelianizationEquiv_of (z : UpperHalfPlane)
    (c : FundamentalGroup ModularTraceQuotient (modularTraceQuotientMk z)) :
    modularTraceMarkedAbelianizationEquiv z (Abelianization.of c) =
      modularTraceMarkedCoordinates z c := rfl

end Markov
