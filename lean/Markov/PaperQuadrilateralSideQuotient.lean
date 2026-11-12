import Markov.QuadrilateralBoundaryExact

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- The exact actual-matrix return condition in the literal paper Q, including
all four original source-side conditions and the identity case. -/
theorem paperIdealQuadrilateral_return_iff (g : SL(2, ℤ))
    (hg : g ∈ modularTraceSubgroup) (z : UpperHalfPlane)
    (hz : z ∈ paperIdealQuadrilateral) :
    g • z ∈ paperIdealQuadrilateral ↔
      g = 1 ∨
      (g = paperGeneratorASL ∧ z ∈ paperRightVerticalSide) ∨
      (g = paperGeneratorASL⁻¹ ∧ z ∈ paperLeftSemicircleSide) ∨
      (g = paperGeneratorBSL ∧ z ∈ paperLeftVerticalSide) ∨
      (g = paperGeneratorBSL⁻¹ ∧ z ∈ paperRightSemicircleSide) := by
  constructor
  · intro hret
    obtain ⟨i, hi⟩ := paperIdealQuadrilateral_return_word g hg z hz hret
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl ⟨hi,
        (paperGeneratorA_quadrilateral_return_iff z hz).mp (by rw [hi] at hret; exact hret)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hi,
        (paperGeneratorA_inv_quadrilateral_return_iff z hz).mp (by rw [hi] at hret; exact hret)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hi,
        (paperGeneratorB_quadrilateral_return_iff z hz).mp (by rw [hi] at hret; exact hret)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hi,
        (paperGeneratorB_inv_quadrilateral_return_iff z hz).mp (by rw [hi] at hret; exact hret)⟩)))
  · rintro (rfl | ⟨rfl, hside⟩ | ⟨rfl, hside⟩ | ⟨rfl, hside⟩ | ⟨rfl, hside⟩)
    · simpa only [one_smul] using hz
    · exact (paperGeneratorA_quadrilateral_return_iff z hz).mpr hside
    · exact (paperGeneratorA_inv_quadrilateral_return_iff z hz).mpr hside
    · exact (paperGeneratorB_quadrilateral_return_iff z hz).mpr hside
    · exact (paperGeneratorB_inv_quadrilateral_return_iff z hz).mpr hside

abbrev PaperQuadrilateralSideQuotient := Quotient paperQuadrilateralSideSetoid

/-- Identity on representatives transports the original-side quotient to the
proved actual orbit-kernel quotient, with both quotient topologies. -/
def paperQuadrilateralSideKernelHomeomorph :
    PaperQuadrilateralSideQuotient ≃ₜ PaperQuadrilateralKernelQuotient where
  toEquiv := Quotient.congrRight fun z w =>
    (paperQuadrilateral_quotient_eq_iff_sideRel z w).symm
  continuous_toFun := continuous_id.quotient_map' fun z w h =>
    (paperQuadrilateral_quotient_eq_iff_sideRel z w).mpr h
  continuous_invFun := continuous_id.quotient_map' fun z w h =>
    (paperQuadrilateral_quotient_eq_iff_sideRel z w).mp h

/-- The literal original A/B side quotient of the literal paper quadrilateral,
with its quotient topology, is homeomorphic to the actual trace quotient. -/
def paperQuadrilateralSideQuotientHomeomorph :
    PaperQuadrilateralSideQuotient ≃ₜ ModularTraceQuotient :=
  paperQuadrilateralSideKernelHomeomorph.trans paperQuadrilateralKernelQuotientHomeomorph

@[simp] theorem paperQuadrilateralSideQuotientHomeomorph_mk
    (z : paperIdealQuadrilateral) :
    paperQuadrilateralSideQuotientHomeomorph (Quotient.mk _ z) =
      modularTraceQuotientMk z.val := rfl

end Markov
