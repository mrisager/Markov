import Markov.PaperQuadrilateralSquareEdges
import Markov.PaperSquareSideAlgebra

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- The independent raw coordinate is the chart's first coordinate. -/
theorem paperSquareRawFirst_eq_chartA (z : UpperHalfPlane) :
    paperSquareRawFirst z = paperSquareChartA z := by
  simp only [paperSquareRawFirst, paperSquareChartA, Complex.normSq_apply,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, pow_two]

/-- The independent raw coordinate is the chart's second coordinate. -/
theorem paperSquareRawSecond_eq_chartB (z : UpperHalfPlane) :
    paperSquareRawSecond z = paperSquareChartB z := by
  simp only [paperSquareRawSecond, paperSquareChartB, Complex.normSq_apply,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, pow_two]

/-- The original A map induces the exact non-affine top-to-bottom edge formula. -/
theorem paperSquareChart_A_side (z : UpperHalfPlane) (hz : z ∈ paperRightVerticalSide) :
    paperSquareChartA (paperGeneratorASL • z) =
      paperSquareSideParameter (paperSquareChartA z) ∧
    paperSquareChartB (paperGeneratorASL • z) = -1 := by
  simpa only [paperSquareRawFirst_eq_chartA, paperSquareRawSecond_eq_chartB] using
    paperSquare_A_coordinates z hz

/-- The original B map induces the exact non-affine right-to-left edge formula. -/
theorem paperSquareChart_B_side (z : UpperHalfPlane) (hz : z ∈ paperLeftVerticalSide) :
    paperSquareChartA (paperGeneratorBSL • z) = -1 ∧
    paperSquareChartB (paperGeneratorBSL • z) =
      paperSquareSideParameter (paperSquareChartB z) := by
  simpa only [paperSquareRawFirst_eq_chartA, paperSquareRawSecond_eq_chartB] using
    paperSquare_B_coordinates z hz

/-- Pair-valued chart formula for the original A side pairing. -/
theorem paperSquareChart_A_pair (z : UpperHalfPlane) (hz : z ∈ paperRightVerticalSide) :
    (paperSquareChartA (paperGeneratorASL • z), paperSquareChartB (paperGeneratorASL • z)) =
      (paperSquareSideParameter (paperSquareChartA z), -1) := by
  exact Prod.ext (paperSquareChart_A_side z hz).1 (paperSquareChart_A_side z hz).2

/-- Pair-valued chart formula for the original B side pairing. -/
theorem paperSquareChart_B_pair (z : UpperHalfPlane) (hz : z ∈ paperLeftVerticalSide) :
    (paperSquareChartA (paperGeneratorBSL • z), paperSquareChartB (paperGeneratorBSL • z)) =
      (-1, paperSquareSideParameter (paperSquareChartB z)) := by
  exact Prod.ext (paperSquareChart_B_side z hz).1 (paperSquareChart_B_side z hz).2

/-- The A formula can be invoked using only the square's top-edge equation. -/
theorem paperSquareChart_A_top (z : UpperHalfPlane) (hz : paperSquareChartB z = 1) :
    (paperSquareChartA (paperGeneratorASL • z), paperSquareChartB (paperGeneratorASL • z)) =
      (paperSquareSideParameter (paperSquareChartA z), -1) :=
  paperSquareChart_A_pair z ((paperSquareChartB_eq_one_iff z).mp hz)

/-- The B formula can be invoked using only the square's right-edge equation. -/
theorem paperSquareChart_B_right (z : UpperHalfPlane) (hz : paperSquareChartA z = 1) :
    (paperSquareChartA (paperGeneratorBSL • z), paperSquareChartB (paperGeneratorBSL • z)) =
      (-1, paperSquareSideParameter (paperSquareChartB z)) :=
  paperSquareChart_B_pair z ((paperSquareChartA_eq_one_iff z).mp hz)

end Markov
