import Markov.PaperQuadrilateralMarkedSideCoordinates

/-! Actual raw-versus-marked side order and the literal positive square
boundary orientation +x,-y,-x,+y. No disk-boundary order field is assumed. -/
noncomputable section
open Set
namespace Markov

/-- The literal raw square coordinate used by the actual disk-chart construction. -/
def paperQuadrilateralRawSideCoordinate (k : Fin 4) (z : paperIdealQuadrilateral) : ℝ :=
  ![paperSquareChartA z, paperSquareChartB z, paperSquareChartA z, paperSquareChartB z] k

/-- The actual bottom/left marked-side normalizer preserves strict order. -/
theorem squareSideNormalizer_one_strictMonoOn :
    StrictMonoOn (SquareSideNormalizer.h 1) (Icc (-1 : ℝ) 1) := by
  intro s hs t ht hst
  have hds : 0 < 5 - 3*s := by linarith [hs.2]
  have hdt : 0 < 5 - 3*t := by linarith [ht.2]
  simp only [SquareSideNormalizer.h, mul_one]
  apply (div_lt_div_iff₀ hds hdt).mpr
  nlinarith

/-- Exact actual side formulas: top/right are unchanged and bottom/left use
that actual increasing Möbius normalizer. -/
theorem paperQuadrilateralMarkedSideCoordinate_raw_formula
    (k : Fin 4) (z : paperIdealQuadrilateral)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide k) :
    paperQuadrilateralMarkedSideCoordinate k z =
      if k = 0 ∨ k = 1 then paperQuadrilateralRawSideCoordinate k z
      else SquareSideNormalizer.h 1 (paperQuadrilateralRawSideCoordinate k z) := by
  fin_cases k
  · change (SquareSideNormalizer.paperPuncturedSquareHomeomorph (paperQuadrilateralToSquare z)).val.1 =
      (paperQuadrilateralToSquare z).val.1
    rw [SquareSideNormalizer.paper_normalizer_top _ ((paperQuadrilateralToSquare_top_iff z).mpr hz)]
  · change (SquareSideNormalizer.paperPuncturedSquareHomeomorph (paperQuadrilateralToSquare z)).val.2 =
      (paperQuadrilateralToSquare z).val.2
    rw [SquareSideNormalizer.paper_normalizer_right _ ((paperQuadrilateralToSquare_right_iff z).mpr hz)]
  · change (SquareSideNormalizer.paperPuncturedSquareHomeomorph (paperQuadrilateralToSquare z)).val.1 =
      SquareSideNormalizer.h 1 (paperQuadrilateralToSquare z).val.1
    rw [SquareSideNormalizer.paper_normalizer_bottom _ ((paperQuadrilateralToSquare_bottom_iff z).mpr hz)]
  · change (SquareSideNormalizer.paperPuncturedSquareHomeomorph (paperQuadrilateralToSquare z)).val.2 =
      SquareSideNormalizer.h 1 (paperQuadrilateralToSquare z).val.2
    rw [SquareSideNormalizer.paper_normalizer_left _ ((paperQuadrilateralToSquare_left_iff z).mpr hz)]

private theorem rawSide_mem (k : Fin 4) (z : paperIdealQuadrilateral) :
    paperQuadrilateralRawSideCoordinate k z ∈ Icc (-1 : ℝ) 1 := by
  have h := paperSquareChart_mem z
  fin_cases k
  · exact abs_le.mp h.1
  · exact abs_le.mp h.2.1
  · exact abs_le.mp h.1
  · exact abs_le.mp h.2.1

/-- Actual marked sorting and actual raw-square order agree on each literal side. -/
theorem paperQuadrilateralMarkedSideCoordinate_raw_lt_iff
    (k : Fin 4) (z w : paperIdealQuadrilateral)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide k)
    (hw : w.val ∈ paperQuadrilateralGeodesicSide k) :
    paperQuadrilateralMarkedSideCoordinate k z < paperQuadrilateralMarkedSideCoordinate k w ↔
      paperQuadrilateralRawSideCoordinate k z < paperQuadrilateralRawSideCoordinate k w := by
  rw [paperQuadrilateralMarkedSideCoordinate_raw_formula k z hz,
    paperQuadrilateralMarkedSideCoordinate_raw_formula k w hw]
  split_ifs
  · rfl
  · exact squareSideNormalizer_one_strictMonoOn.lt_iff_lt (rawSide_mem k z) (rawSide_mem k w)

/-- The actual square-boundary oriented coordinate: +x,-y,-x,+y on0,1,2,3. -/
def paperQuadrilateralBoundarySideCoordinate (k : Fin 4) (z : paperIdealQuadrilateral) : ℝ :=
  ![paperQuadrilateralMarkedSideCoordinate 0 z, -paperQuadrilateralMarkedSideCoordinate 1 z,
    -paperQuadrilateralMarkedSideCoordinate 2 z, paperQuadrilateralMarkedSideCoordinate 3 z] k

/-- Literal positive boundary traversal, with each oriented parameter increasing. -/
def paperQuadrilateralBoundarySidePoint (k : Fin 4) (r : ℝ) : ℝ × ℝ :=
  ![(r,1),(1,-r),(-r,-1),(-1,r)] k

/-- The orientation is proved on actual marked-square points, not declared
as an unverified boundary-order predicate. -/
theorem paperQuadrilateralBoundarySideCoordinate_shape (k : Fin 4) (z : paperIdealQuadrilateral)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide k) :
    (paperMarkedQuadrilateralSquareHomeomorph z).val =
      paperQuadrilateralBoundarySidePoint k (paperQuadrilateralBoundarySideCoordinate k z) := by
  have he := paperQuadrilateralMarkedSideCoordinate_shape k z hz
  fin_cases k
  · exact he
  · simpa [paperQuadrilateralBoundarySidePoint, paperQuadrilateralBoundarySideCoordinate,
      paperQuadrilateralMarkedSidePoint] using he
  · simpa [paperQuadrilateralBoundarySidePoint, paperQuadrilateralBoundarySideCoordinate,
      paperQuadrilateralMarkedSidePoint] using he
  · exact he

/-- Every actual oriented side coordinate lies strictly between its two corners. -/
theorem paperQuadrilateralBoundarySideCoordinate_bounds (k : Fin 4) (z : paperIdealQuadrilateral)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide k) :
    -1 < paperQuadrilateralBoundarySideCoordinate k z ∧
      paperQuadrilateralBoundarySideCoordinate k z < 1 := by
  fin_cases k
  · exact paperQuadrilateralMarkedSideCoordinate_bounds 0 z hz
  · have hb := paperQuadrilateralMarkedSideCoordinate_bounds 1 z hz
    change -1 < -paperQuadrilateralMarkedSideCoordinate 1 z ∧
      -paperQuadrilateralMarkedSideCoordinate 1 z < 1
    constructor <;> linarith [hb.1,hb.2]
  · have hb := paperQuadrilateralMarkedSideCoordinate_bounds 2 z hz
    change -1 < -paperQuadrilateralMarkedSideCoordinate 2 z ∧
      -paperQuadrilateralMarkedSideCoordinate 2 z < 1
    constructor <;> linarith [hb.1,hb.2]
  · exact paperQuadrilateralMarkedSideCoordinate_bounds 3 z hz

end Markov
