import Markov.PaperMarkedSquareStandardRelations
import Markov.StandardPuncturedTorusQuotient
import Markov.PaperQuadrilateralSideQuotient

noncomputable section
namespace Markov

/-- Transport of the literal paper side quotient through the marked square chart. -/
def paperMarkedSquareSideQuotientHomeomorph :
    PaperQuadrilateralSideQuotient ≃ₜ StandardPuncturedSquareSideQuotient where
  toEquiv := Quotient.congr paperMarkedQuadrilateralSquareHomeomorph.toEquiv
    (fun z w => (paperMarkedSquare_standardRel_iff z w).symm)
  continuous_toFun := paperMarkedQuadrilateralSquareHomeomorph.continuous.quotient_map'
    (fun z w h => (paperMarkedSquare_standardRel_iff z w).mpr h)
  continuous_invFun := paperMarkedQuadrilateralSquareHomeomorph.symm.continuous.quotient_map'
    (fun p q h => by
      apply (paperMarkedSquare_standardRel_iff _ _).mp
      simpa using h)

/-- The original paper side quotient is homeomorphic to the literal standard torus minus its origin. -/
def paperSideQuotientPuncturedTorusHomeomorph :
    PaperQuadrilateralSideQuotient ≃ₜ StandardPuncturedTorus :=
  paperMarkedSquareSideQuotientHomeomorph.trans standardPuncturedSquareQuotientHomeomorph

/-- The actual trace quotient is homeomorphic to the literal standard torus minus its origin. -/
def modularTraceQuotientPuncturedTorusHomeomorph :
    ModularTraceQuotient ≃ₜ StandardPuncturedTorus :=
  paperQuadrilateralSideQuotientHomeomorph.symm.trans paperSideQuotientPuncturedTorusHomeomorph

/-- The marked construction retains a literal representative formula on the original side quotient. -/
theorem paperSideQuotientPuncturedTorusHomeomorph_mk (z : paperIdealQuadrilateral) :
    paperSideQuotientPuncturedTorusHomeomorph (Quotient.mk _ z) =
      standardPuncturedTorusMap (paperMarkedQuadrilateralSquareHomeomorph z) := rfl

/-- The homeomorphism on the actual orbit class agrees with the normalized literal chart. -/
theorem modularTraceQuotientPuncturedTorusHomeomorph_mk (z : paperIdealQuadrilateral) :
    modularTraceQuotientPuncturedTorusHomeomorph (modularTraceQuotientMk z.val) =
      standardPuncturedTorusMap (paperMarkedQuadrilateralSquareHomeomorph z) := by
  rw [← paperQuadrilateralSideQuotientHomeomorph_mk z]
  change paperSideQuotientPuncturedTorusHomeomorph
    (paperQuadrilateralSideQuotientHomeomorph.symm
      (paperQuadrilateralSideQuotientHomeomorph (Quotient.mk _ z))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

end Markov

