import Markov.PaperMarkedSquareChart
import Markov.PaperQuadrilateralSideRelation

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- Ordinary directed top/bottom and right/left edge identifications on the corner-deleted square. -/
def PaperSquareSideStep (p q : paperPuncturedSquare) : Prop :=
  (p.val.2 = 1 ∧ q.val.2 = -1 ∧ p.val.1 = q.val.1) ∨
  (p.val.1 = 1 ∧ q.val.1 = -1 ∧ p.val.2 = q.val.2)

theorem paperMarkedSquare_top_iff (z : paperIdealQuadrilateral) :
    (paperMarkedQuadrilateralSquareHomeomorph z).val.2 = 1 ↔ z.val ∈ paperRightVerticalSide := by
  have hh (p : paperPuncturedSquare) :
      (SquareSideNormalizer.paperPuncturedSquareHomeomorph p).val.2 = 1 ↔ p.val.2 = 1 := by
    constructor
    · intro hp
      have he := SquareSideNormalizer.paper_normalizer_top
        (SquareSideNormalizer.paperPuncturedSquareHomeomorph p) hp
      have he' := SquareSideNormalizer.paperPuncturedSquareHomeomorph.injective he
      rwa [he'] at hp
    · intro hp
      rw [SquareSideNormalizer.paper_normalizer_top p hp]
      exact hp
  change (SquareSideNormalizer.paperPuncturedSquareHomeomorph (paperQuadrilateralToSquare z)).val.2 = 1 ↔ _
  rw [hh]
  exact paperSquareChartB_eq_one_iff z.val

theorem paperMarkedSquare_right_iff (z : paperIdealQuadrilateral) :
    (paperMarkedQuadrilateralSquareHomeomorph z).val.1 = 1 ↔ z.val ∈ paperLeftVerticalSide := by
  have hh (p : paperPuncturedSquare) :
      (SquareSideNormalizer.paperPuncturedSquareHomeomorph p).val.1 = 1 ↔ p.val.1 = 1 := by
    constructor
    · intro hp
      have he := SquareSideNormalizer.paper_normalizer_right
        (SquareSideNormalizer.paperPuncturedSquareHomeomorph p) hp
      have he' := SquareSideNormalizer.paperPuncturedSquareHomeomorph.injective he
      rwa [he'] at hp
    · intro hp
      rw [SquareSideNormalizer.paper_normalizer_right p hp]
      exact hp
  change (SquareSideNormalizer.paperPuncturedSquareHomeomorph (paperQuadrilateralToSquare z)).val.1 = 1 ↔ _
  rw [hh]
  exact paperSquareChartA_eq_one_iff z.val

theorem paperMarkedSquare_A_pair_iff (z w : paperIdealQuadrilateral) :
    ((paperMarkedQuadrilateralSquareHomeomorph z).val.2 = 1 ∧
      (paperMarkedQuadrilateralSquareHomeomorph w).val.2 = -1 ∧
      (paperMarkedQuadrilateralSquareHomeomorph z).val.1 =
        (paperMarkedQuadrilateralSquareHomeomorph w).val.1) ↔
    (z.val ∈ paperRightVerticalSide ∧ paperGeneratorASL • z.val = w.val) := by
  constructor
  · rintro ⟨hzTop, hwBottom, hparam⟩
    have hz := (paperMarkedSquare_top_iff z).mp hzTop
    let u : paperIdealQuadrilateral := ⟨paperGeneratorASL • z.val,
      (paperGeneratorA_quadrilateral_return_iff z.val z.property).mpr hz⟩
    have hp := paperMarkedSquare_A_pair z u hz rfl
    have hu : paperMarkedQuadrilateralSquareHomeomorph u =
        paperMarkedQuadrilateralSquareHomeomorph w := by
      apply Subtype.ext
      apply Prod.ext
      · exact (congrArg Prod.fst hp.2).trans ((congrArg Prod.fst hp.1).symm.trans hparam)
      · exact (congrArg Prod.snd hp.2).trans hwBottom.symm
    have he := paperMarkedQuadrilateralSquareHomeomorph.injective hu
    exact ⟨hz, congrArg Subtype.val he⟩
  · rintro ⟨hz, hact⟩
    have hp := paperMarkedSquare_A_pair z w hz hact
    exact ⟨congrArg Prod.snd hp.1, congrArg Prod.snd hp.2,
      (congrArg Prod.fst hp.1).trans (congrArg Prod.fst hp.2).symm⟩

theorem paperMarkedSquare_B_pair_iff (z w : paperIdealQuadrilateral) :
    ((paperMarkedQuadrilateralSquareHomeomorph z).val.1 = 1 ∧
      (paperMarkedQuadrilateralSquareHomeomorph w).val.1 = -1 ∧
      (paperMarkedQuadrilateralSquareHomeomorph z).val.2 =
        (paperMarkedQuadrilateralSquareHomeomorph w).val.2) ↔
    (z.val ∈ paperLeftVerticalSide ∧ paperGeneratorBSL • z.val = w.val) := by
  constructor
  · rintro ⟨hzRight, hwLeft, hparam⟩
    have hz := (paperMarkedSquare_right_iff z).mp hzRight
    let u : paperIdealQuadrilateral := ⟨paperGeneratorBSL • z.val,
      (paperGeneratorB_quadrilateral_return_iff z.val z.property).mpr hz⟩
    have hp := paperMarkedSquare_B_pair z u hz rfl
    have hu : paperMarkedQuadrilateralSquareHomeomorph u =
        paperMarkedQuadrilateralSquareHomeomorph w := by
      apply Subtype.ext
      apply Prod.ext
      · exact (congrArg Prod.fst hp.2).trans hwLeft.symm
      · exact (congrArg Prod.snd hp.2).trans ((congrArg Prod.snd hp.1).symm.trans hparam)
    have he := paperMarkedQuadrilateralSquareHomeomorph.injective hu
    exact ⟨hz, congrArg Subtype.val he⟩
  · rintro ⟨hz, hact⟩
    have hp := paperMarkedSquare_B_pair z w hz hact
    exact ⟨congrArg Prod.fst hp.1, congrArg Prod.fst hp.2,
      (congrArg Prod.snd hp.1).trans (congrArg Prod.snd hp.2).symm⟩

theorem paperMarkedSquare_sideStep_iff (z w : paperIdealQuadrilateral) :
    PaperSquareSideStep (paperMarkedQuadrilateralSquareHomeomorph z)
      (paperMarkedQuadrilateralSquareHomeomorph w) ↔ PaperQuadrilateralSideStep z w := by
  exact or_congr (paperMarkedSquare_A_pair_iff z w) (paperMarkedSquare_B_pair_iff z w)


/-- The equivalence relation generated by the directed ordinary edge identifications. -/
def PaperSquareSideRel : paperPuncturedSquare → paperPuncturedSquare → Prop :=
  Relation.EqvGen PaperSquareSideStep

def paperSquareSideSetoid : Setoid paperPuncturedSquare :=
  Relation.EqvGen.setoid PaperSquareSideStep

theorem paperMarkedSquare_sideRel_forward {z w : paperIdealQuadrilateral}
    (h : PaperQuadrilateralSideRel z w) :
    PaperSquareSideRel (paperMarkedQuadrilateralSquareHomeomorph z)
      (paperMarkedQuadrilateralSquareHomeomorph w) := by
  induction h with
  | rel z w h => exact Relation.EqvGen.rel _ _ ((paperMarkedSquare_sideStep_iff z w).mpr h)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem paperMarkedSquare_sideRel_inverse {p q : paperPuncturedSquare}
    (h : PaperSquareSideRel p q) :
    PaperQuadrilateralSideRel (paperMarkedQuadrilateralSquareHomeomorph.symm p)
      (paperMarkedQuadrilateralSquareHomeomorph.symm q) := by
  induction h with
  | rel p q h =>
    apply Relation.EqvGen.rel
    apply (paperMarkedSquare_sideStep_iff _ _).mp
    simpa using h
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- The marked chart conjugates the full literal A/B generated relation, in both directions. -/
theorem paperMarkedSquare_sideRel_iff (z w : paperIdealQuadrilateral) :
    PaperSquareSideRel (paperMarkedQuadrilateralSquareHomeomorph z)
      (paperMarkedQuadrilateralSquareHomeomorph w) ↔ PaperQuadrilateralSideRel z w := by
  constructor
  · intro h
    simpa using paperMarkedSquare_sideRel_inverse h
  · exact paperMarkedSquare_sideRel_forward

end Markov

