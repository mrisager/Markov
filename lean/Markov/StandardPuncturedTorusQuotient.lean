import Markov.StandardTorusSquare
import Markov.StandardSquareEdgeKernel

noncomputable section
open Topology
namespace Markov

/-- The actual standard-torus projection has exactly the ordinary opposite-edge kernel. -/
theorem standardPuncturedTorusMap_eq_iff_edgeRel (p q : paperPuncturedSquare) :
    standardPuncturedTorusMap p = standardPuncturedTorusMap q ↔
      standardSquareOppositeEdgeRel p q := by
  rw [Subtype.ext_iff]
  exact standardSquare_scalar_kernel_iff p q

abbrev StandardPuncturedSquareSideQuotient := Quotient standardSquareOppositeEdgeSetoid

/-- Identity on square representatives changes the proved edge setoid to the
actual projection kernel without changing either quotient topology. -/
def standardPuncturedSquareSideKernelHomeomorph :
    StandardPuncturedSquareSideQuotient ≃ₜ
      Quotient (Setoid.ker standardPuncturedTorusMap) where
  toEquiv := Quotient.congrRight fun p q =>
    (standardPuncturedTorusMap_eq_iff_edgeRel p q).symm
  continuous_toFun := continuous_id.quotient_map' fun p q h =>
    (standardPuncturedTorusMap_eq_iff_edgeRel p q).mpr h
  continuous_invFun := continuous_id.quotient_map' fun p q h =>
    (standardPuncturedTorusMap_eq_iff_edgeRel p q).mp h

/-- The ordinary opposite-edge quotient of the literal corners-removed square
is homeomorphic to the actual standard torus with one point removed. -/
def standardPuncturedSquareQuotientHomeomorph :
    StandardPuncturedSquareSideQuotient ≃ₜ StandardPuncturedTorus :=
  standardPuncturedSquareSideKernelHomeomorph.trans
    (show IsQuotientMap
      (⟨standardPuncturedTorusMap, continuous_standardPuncturedTorusMap⟩ :
        C(paperPuncturedSquare, StandardPuncturedTorus)) from
          standardPuncturedTorusMap_isQuotientMap).homeomorph

/-- The quotient homeomorphism retains the literal affine circle coordinates. -/
theorem standardPuncturedSquareQuotientHomeomorph_mk (p : paperPuncturedSquare) :
    standardPuncturedSquareQuotientHomeomorph (Quotient.mk _ p) =
      standardPuncturedTorusMap p := rfl

/-- Explicit coordinates of every representative under the standard quotient homeomorphism. -/
theorem standardPuncturedSquareQuotientHomeomorph_mk_coe (p : paperPuncturedSquare) :
    (standardPuncturedSquareQuotientHomeomorph (Quotient.mk _ p)).1 =
      (standardCircleSquareScalar p.1.1, standardCircleSquareScalar p.1.2) := rfl

end Markov
