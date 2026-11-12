import Markov.PaperQuadrilateralBoundaryOrientation
import Markov.PaperQuadrilateralDiskChart
import Markov.RawSquareQuarterTurns

/-! Actual raw-square frames at every original Q corner. The literal complex
quarter turn carries each selected side to TOP and its next side to RIGHT.
Actual marked boundary order agrees with the proved raw oriented coordinate.
These are coordinate identities, not nearest-pair or diagram fields. -/

noncomputable section
open Set
namespace Markov

/-- The literal next-side permutation in TOP,RIGHT,BOTTOM,LEFT order. -/
def paperQuadrilateralNextSide : Equiv.Perm (Fin 4) where
  toFun := ![1, 2, 3, 0]
  invFun := ![3, 0, 1, 2]
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

theorem paperQuadrilateralNextSide_ne (k : Fin 4) :
    paperQuadrilateralNextSide k ≠ k := by
  fin_cases k <;> decide

/-- The actual raw square's clockwise free coordinate: +A,-B,-A,+B. -/
def paperQuadrilateralRawBoundarySideCoordinate (k : Fin 4)
    (z : paperIdealQuadrilateral) : ℝ :=
  ![paperSquareChartA z, -paperSquareChartB z,
    -paperSquareChartA z, paperSquareChartB z] k

/-- Actual marked boundary order and actual oriented raw-square order agree
on every original side, including the two normalized target sides. -/
theorem paperQuadrilateralBoundarySideCoordinate_raw_lt_iff
    (k : Fin 4) (z w : paperIdealQuadrilateral)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide k)
    (hw : w.val ∈ paperQuadrilateralGeodesicSide k) :
    paperQuadrilateralBoundarySideCoordinate k z <
        paperQuadrilateralBoundarySideCoordinate k w ↔
      paperQuadrilateralRawBoundarySideCoordinate k z <
        paperQuadrilateralRawBoundarySideCoordinate k w := by
  fin_cases k
  · exact paperQuadrilateralMarkedSideCoordinate_raw_lt_iff 0 z w hz hw
  · simpa [paperQuadrilateralBoundarySideCoordinate,
      paperQuadrilateralRawBoundarySideCoordinate, paperQuadrilateralRawSideCoordinate] using
        paperQuadrilateralMarkedSideCoordinate_raw_lt_iff 1 w z hw hz
  · simpa [paperQuadrilateralBoundarySideCoordinate,
      paperQuadrilateralRawBoundarySideCoordinate, paperQuadrilateralRawSideCoordinate] using
        paperQuadrilateralMarkedSideCoordinate_raw_lt_iff 2 w z hw hz
  · exact paperQuadrilateralMarkedSideCoordinate_raw_lt_iff 3 z w hz hw

/-- The same actual order comparison with weak inequalities. -/
theorem paperQuadrilateralBoundarySideCoordinate_raw_le_iff
    (k : Fin 4) (z w : paperIdealQuadrilateral)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide k)
    (hw : w.val ∈ paperQuadrilateralGeodesicSide k) :
    paperQuadrilateralBoundarySideCoordinate k z ≤
        paperQuadrilateralBoundarySideCoordinate k w ↔
      paperQuadrilateralRawBoundarySideCoordinate k z ≤
        paperQuadrilateralRawBoundarySideCoordinate k w := by
  simpa only [not_lt] using
    not_congr (paperQuadrilateralBoundarySideCoordinate_raw_lt_iff k w z hw hz)

/-- The actual oriented raw coordinate is strictly between the deleted corners. -/
theorem paperQuadrilateralRawBoundarySideCoordinate_bounds
    (k : Fin 4) (z : paperIdealQuadrilateral)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide k) :
    -1 < paperQuadrilateralRawBoundarySideCoordinate k z ∧
      paperQuadrilateralRawBoundarySideCoordinate k z < 1 := by
  fin_cases k
  · exact paperPuncturedSquare_horizontal_param (paperQuadrilateralToSquare z)
      (Or.inl ((paperQuadrilateralToSquare_top_iff z).mpr hz))
  · have hb := paperPuncturedSquare_vertical_param (paperQuadrilateralToSquare z)
      (Or.inl ((paperQuadrilateralToSquare_right_iff z).mpr hz))
    change -1 < -paperSquareChartB z ∧ -paperSquareChartB z < 1
    change -1 < paperSquareChartB z ∧ paperSquareChartB z < 1 at hb
    constructor <;> linarith [hb.1, hb.2]
  · have hb := paperPuncturedSquare_horizontal_param (paperQuadrilateralToSquare z)
      (Or.inr ((paperQuadrilateralToSquare_bottom_iff z).mpr hz))
    change -1 < -paperSquareChartA z ∧ -paperSquareChartA z < 1
    change -1 < paperSquareChartA z ∧ paperSquareChartA z < 1 at hb
    constructor <;> linarith [hb.1, hb.2]
  · exact paperPuncturedSquare_vertical_param (paperQuadrilateralToSquare z)
      (Or.inr ((paperQuadrilateralToSquare_left_iff z).mpr hz))

/-- The actual original Q raw square point in the literal selected side frame. -/
def paperQuadrilateralRawSideFrame (k : Fin 4) (z : paperIdealQuadrilateral) : ℂ :=
  rawSquareQuarterTurn k (paperQuadrilateralComplexSquare z)

/-- The selected-frame real coordinate is the selected side's raw oriented
free-coordinate formula, for every actual Q point. -/
theorem paperQuadrilateralRawSideFrame_re (k : Fin 4) (z : paperIdealQuadrilateral) :
    (paperQuadrilateralRawSideFrame k z).re =
      paperQuadrilateralRawBoundarySideCoordinate k z := by
  fin_cases k <;>
    simp [paperQuadrilateralRawSideFrame, rawSquareQuarterTurn,
      paperQuadrilateralComplexSquare, paperQuadrilateralRawBoundarySideCoordinate,
      Complex.mul_re]

/-- The selected-frame imaginary coordinate is minus the next side's raw
oriented free-coordinate formula, for every actual Q point. -/
theorem paperQuadrilateralRawSideFrame_im (k : Fin 4) (z : paperIdealQuadrilateral) :
    (paperQuadrilateralRawSideFrame k z).im =
      -paperQuadrilateralRawBoundarySideCoordinate (paperQuadrilateralNextSide k) z := by
  fin_cases k <;>
    simp [paperQuadrilateralRawSideFrame, rawSquareQuarterTurn,
      paperQuadrilateralComplexSquare, paperQuadrilateralRawBoundarySideCoordinate,
      paperQuadrilateralNextSide, Complex.mul_im]

/-- All four relative-side identifications are actual equivalences. After
turning side k to TOP, side j has the literal relative label j-k modulo four. -/
theorem paperQuadrilateralRawSideFrame_side_iff (k j : Fin 4)
    (z : paperIdealQuadrilateral) :
    ![(paperQuadrilateralRawSideFrame k z).im = 1,
      (paperQuadrilateralRawSideFrame k z).re = 1,
      (paperQuadrilateralRawSideFrame k z).im = -1,
      (paperQuadrilateralRawSideFrame k z).re = -1] (j - k) ↔
        z.val ∈ paperQuadrilateralGeodesicSide j := by
  fin_cases k <;> fin_cases j
  all_goals first
    | simpa [paperQuadrilateralRawSideFrame, rawSquareQuarterTurn,
        paperQuadrilateralComplexSquare, paperQuadrilateralGeodesicSide,
        Complex.mul_re, Complex.mul_im, neg_eq_iff_eq_neg] using paperSquareChartB_eq_one_iff z.val
    | simpa [paperQuadrilateralRawSideFrame, rawSquareQuarterTurn,
        paperQuadrilateralComplexSquare, paperQuadrilateralGeodesicSide,
        Complex.mul_re, Complex.mul_im, neg_eq_iff_eq_neg] using paperSquareChartA_eq_one_iff z.val
    | simpa [paperQuadrilateralRawSideFrame, rawSquareQuarterTurn,
        paperQuadrilateralComplexSquare, paperQuadrilateralGeodesicSide,
        Complex.mul_re, Complex.mul_im, neg_eq_iff_eq_neg] using paperSquareChartB_eq_neg_one_iff z.val
    | simpa [paperQuadrilateralRawSideFrame, rawSquareQuarterTurn,
        paperQuadrilateralComplexSquare, paperQuadrilateralGeodesicSide,
        Complex.mul_re, Complex.mul_im, neg_eq_iff_eq_neg] using paperSquareChartA_eq_neg_one_iff z.val

/-- An actual point on selected side k has the displayed actual TOP shape. -/
theorem paperQuadrilateralRawSideFrame_top (k : Fin 4) (z : paperIdealQuadrilateral)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide k) :
    (paperQuadrilateralRawSideFrame k z).im = 1 ∧
      (paperQuadrilateralRawSideFrame k z).re =
        paperQuadrilateralRawBoundarySideCoordinate k z := by
  refine ⟨?_, paperQuadrilateralRawSideFrame_re k z⟩
  have h := (paperQuadrilateralRawSideFrame_side_iff k k z).mpr hz
  fin_cases k <;> simpa using h

/-- An actual point on the literal next side has the displayed actual RIGHT
shape, with the negative of that side's raw oriented coordinate as height. -/
theorem paperQuadrilateralRawSideFrame_right (k : Fin 4) (z : paperIdealQuadrilateral)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide (paperQuadrilateralNextSide k)) :
    (paperQuadrilateralRawSideFrame k z).re = 1 ∧
      (paperQuadrilateralRawSideFrame k z).im =
        -paperQuadrilateralRawBoundarySideCoordinate (paperQuadrilateralNextSide k) z := by
  refine ⟨?_, paperQuadrilateralRawSideFrame_im k z⟩
  have h := (paperQuadrilateralRawSideFrame_side_iff k (paperQuadrilateralNextSide k) z).mpr hz
  fin_cases k <;> simpa [paperQuadrilateralNextSide] using h

end Markov
