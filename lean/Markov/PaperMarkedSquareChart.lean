import Markov.PaperPuncturedSquareNormalizer
import Markov.PaperQuadrilateralSquareSides

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- The actual quadrilateral chart after normalizing its literal A/B edge parameters. -/
def paperMarkedQuadrilateralSquareHomeomorph : paperIdealQuadrilateral ≃ₜ paperPuncturedSquare :=
  paperQuadrilateralSquareHomeomorph.trans SquareSideNormalizer.paperPuncturedSquareHomeomorph

/-- The original A pairing becomes the ordinary top-to-bottom square pairing. -/
theorem paperMarkedSquare_A_pair (z w : paperIdealQuadrilateral)
    (hz : z.val ∈ paperRightVerticalSide)
    (hact : paperGeneratorASL • z.val = w.val) :
    (paperMarkedQuadrilateralSquareHomeomorph z).val = (paperSquareChartA z.val, 1) ∧
    (paperMarkedQuadrilateralSquareHomeomorph w).val = (paperSquareChartA z.val, -1) := by
  have hb : paperSquareChartB z.val = 1 := (paperSquareChartB_eq_one_iff z.val).mpr hz
  constructor
  · change (SquareSideNormalizer.paperPuncturedSquareHomeomorph (paperQuadrilateralToSquare z)).val = _
    rw [SquareSideNormalizer.paper_normalizer_top (paperQuadrilateralToSquare z) hb]
    change (paperSquareChartA z.val, paperSquareChartB z.val) = _
    rw [hb]
  · change (SquareSideNormalizer.paperPuncturedSquareHomeomorph (paperQuadrilateralToSquare w)).val = _
    apply SquareSideNormalizer.paper_normalizer_bottom_paired
      (paperQuadrilateralToSquare w) (paperSquareChartA z.val)
      (abs_le.mp (paperQuadrilateralToSquare z).property.1)
    have hp := paperSquareChart_A_pair z.val hz
    rw [hact] at hp
    exact hp

/-- The original B pairing becomes the ordinary right-to-left square pairing. -/
theorem paperMarkedSquare_B_pair (z w : paperIdealQuadrilateral)
    (hz : z.val ∈ paperLeftVerticalSide)
    (hact : paperGeneratorBSL • z.val = w.val) :
    (paperMarkedQuadrilateralSquareHomeomorph z).val = (1, paperSquareChartB z.val) ∧
    (paperMarkedQuadrilateralSquareHomeomorph w).val = (-1, paperSquareChartB z.val) := by
  have ha : paperSquareChartA z.val = 1 := (paperSquareChartA_eq_one_iff z.val).mpr hz
  constructor
  · change (SquareSideNormalizer.paperPuncturedSquareHomeomorph (paperQuadrilateralToSquare z)).val = _
    rw [SquareSideNormalizer.paper_normalizer_right (paperQuadrilateralToSquare z) ha]
    change (paperSquareChartA z.val, paperSquareChartB z.val) = _
    rw [ha]
  · change (SquareSideNormalizer.paperPuncturedSquareHomeomorph (paperQuadrilateralToSquare w)).val = _
    apply SquareSideNormalizer.paper_normalizer_left_paired
      (paperQuadrilateralToSquare w) (paperSquareChartB z.val)
      (abs_le.mp (paperQuadrilateralToSquare z).property.2.1)
    have hp := paperSquareChart_B_pair z.val hz
    rw [hact] at hp
    exact hp

end Markov

