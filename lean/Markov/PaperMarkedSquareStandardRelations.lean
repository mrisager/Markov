import Markov.PaperMarkedSquareRelations
import Markov.StandardSquareEdgeKernel

noncomputable section
namespace Markov

theorem paperSquareSideStep_standard {p q : paperPuncturedSquare}
    (h : PaperSquareSideStep p q) : standardSquareOppositeEdgeStep p q := by
  rcases h with ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩
  · exact Or.inl ⟨he, Or.inr ⟨h1, h2⟩⟩
  · exact Or.inr ⟨he, Or.inr ⟨h1, h2⟩⟩

theorem standardSquareOppositeEdgeStep_paperSideRel {p q : paperPuncturedSquare}
    (h : standardSquareOppositeEdgeStep p q) : PaperSquareSideRel p q := by
  rcases h with ⟨he, h⟩ | ⟨he, h⟩
  · rcases h with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inl ⟨hq, hp, he.symm⟩))
    · exact Relation.EqvGen.rel _ _ (Or.inl ⟨hp, hq, he⟩)
  · rcases h with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr ⟨hq, hp, he.symm⟩))
    · exact Relation.EqvGen.rel _ _ (Or.inr ⟨hp, hq, he⟩)

/-- Directed ordinary edge identifications generate the usual symmetric opposite-edge relation. -/
theorem paperSquareSideRel_iff_standard (p q : paperPuncturedSquare) :
    PaperSquareSideRel p q ↔ standardSquareOppositeEdgeRel p q := by
  constructor
  · exact Relation.EqvGen.mono (fun _ _ => paperSquareSideStep_standard)
  · intro h
    induction h with
    | rel _ _ h => exact standardSquareOppositeEdgeStep_paperSideRel h
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- The actual marked chart exactly conjugates the original paper relation to standard square gluing. -/
theorem paperMarkedSquare_standardRel_iff (z w : paperIdealQuadrilateral) :
    standardSquareOppositeEdgeRel (paperMarkedQuadrilateralSquareHomeomorph z)
      (paperMarkedQuadrilateralSquareHomeomorph w) ↔ PaperQuadrilateralSideRel z w :=
  (paperSquareSideRel_iff_standard _ _).symm.trans (paperMarkedSquare_sideRel_iff z w)

end Markov

