import Markov.PaperQuadrilateralSquareChart

noncomputable section
namespace Markov

/-- The chart's top edge is exactly the original right vertical side. -/
theorem paperSquareChartB_eq_one_iff (z : UpperHalfPlane) :
    paperSquareChartB z = 1 ↔ z ∈ paperRightVerticalSide := by
  have hD : Complex.normSq (z : ℂ) + 1 ≠ 0 := ne_of_gt (by linarith [z.normSq_pos])
  unfold paperSquareChartB
  rw [div_eq_iff hD]
  change _ ↔ z.re = 1
  constructor <;> intro h <;> linarith

/-- The chart's right edge is exactly the original left vertical side. -/
theorem paperSquareChartA_eq_one_iff (z : UpperHalfPlane) :
    paperSquareChartA z = 1 ↔ z ∈ paperLeftVerticalSide := by
  have hD : Complex.normSq (z : ℂ) + 1 ≠ 0 := ne_of_gt (by linarith [z.normSq_pos])
  unfold paperSquareChartA
  rw [div_eq_iff hD]
  change _ ↔ z.re = -1
  constructor <;> intro h <;> linarith

/-- The chart's left edge is exactly the original right semicircle side. -/
theorem paperSquareChartA_eq_neg_one_iff (z : UpperHalfPlane) :
    paperSquareChartA z = -1 ↔ z ∈ paperRightSemicircleSide := by
  have hD : Complex.normSq (z : ℂ) + 1 ≠ 0 := ne_of_gt (by linarith [z.normSq_pos])
  unfold paperSquareChartA
  rw [div_eq_iff hD]
  change _ ↔ z.re ^ 2 - z.re + z.im ^ 2 = 0
  simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  constructor <;> intro h <;> nlinarith

/-- The chart's bottom edge is exactly the original left semicircle side. -/
theorem paperSquareChartB_eq_neg_one_iff (z : UpperHalfPlane) :
    paperSquareChartB z = -1 ↔ z ∈ paperLeftSemicircleSide := by
  have hD : Complex.normSq (z : ℂ) + 1 ≠ 0 := ne_of_gt (by linarith [z.normSq_pos])
  unfold paperSquareChartB
  rw [div_eq_iff hD]
  change _ ↔ z.re ^ 2 + z.re + z.im ^ 2 = 0
  simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  constructor <;> intro h <;> nlinarith

/-- Every point of a horizontal edge has an open-interval parameter. -/
theorem paperPuncturedSquare_horizontal_param (p : paperPuncturedSquare)
    (hb : p.1.2 = 1 ∨ p.1.2 = -1) : -1 < p.1.1 ∧ p.1.1 < 1 := by
  have hs := p.2.2.2
  rcases hb with h | h <;> rw [h] at hs <;> constructor <;> nlinarith

/-- Every point of a vertical edge has an open-interval parameter. -/
theorem paperPuncturedSquare_vertical_param (p : paperPuncturedSquare)
    (ha : p.1.1 = 1 ∨ p.1.1 = -1) : -1 < p.1.2 ∧ p.1.2 < 1 := by
  have hs := p.2.2.2
  rcases ha with h | h <;> rw [h] at hs <;> constructor <;> nlinarith

/-- Exact forward-chart identification of the original A source side. -/
theorem paperQuadrilateralToSquare_top_iff (z : paperIdealQuadrilateral) :
    (paperQuadrilateralToSquare z).1.2 = 1 ↔ z.1 ∈ paperRightVerticalSide :=
  paperSquareChartB_eq_one_iff z.1

/-- Exact forward-chart identification of the original B source side. -/
theorem paperQuadrilateralToSquare_right_iff (z : paperIdealQuadrilateral) :
    (paperQuadrilateralToSquare z).1.1 = 1 ↔ z.1 ∈ paperLeftVerticalSide :=
  paperSquareChartA_eq_one_iff z.1

/-- Exact forward-chart identification of the original B target side. -/
theorem paperQuadrilateralToSquare_left_iff (z : paperIdealQuadrilateral) :
    (paperQuadrilateralToSquare z).1.1 = -1 ↔ z.1 ∈ paperRightSemicircleSide :=
  paperSquareChartA_eq_neg_one_iff z.1

/-- Exact forward-chart identification of the original A target side. -/
theorem paperQuadrilateralToSquare_bottom_iff (z : paperIdealQuadrilateral) :
    (paperQuadrilateralToSquare z).1.2 = -1 ↔ z.1 ∈ paperLeftSemicircleSide :=
  paperSquareChartB_eq_neg_one_iff z.1

end Markov
