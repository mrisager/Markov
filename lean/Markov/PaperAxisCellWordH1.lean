import Markov.PaperAxisOrderedCellWord
import Markov.ModularH1Transport

/-! The actual ordered side word has the genuine original-marked singular H1
coordinates of the actual axis-period loop. No simple-diagram classification
or inference from H1 to a nonabelian class is made. -/
noncomputable section
open Set Topology
open scoped MatrixGroups
namespace Markov

/-- Signed original A/B coordinates of the literal alphabet [A^-1,B^-1,A,B]. -/
def paperAxisCellLetterCoordinates (k : Fin 4) : ℤ × ℤ :=
  ![(-1, 0), (0, -1), (1, 0), (0, 1)] k

/-- Each actual neighboring deck matrix has exactly its signed original
A/B coordinates under the checked actual abelianization marking. -/
theorem paperQuadrilateralSideNeighbor_coordinates (k : Fin 4) :
    paperTraceAbelianizationCoordinates (paperQuadrilateralSideNeighbor k) =
      Multiplicative.ofAdd (paperAxisCellLetterCoordinates k) := by
  fin_cases k
  · change paperTraceAbelianizationCoordinates (paperQuadrilateralSideNeighbor 0) =
      Multiplicative.ofAdd ((-1, 0) : ℤ × ℤ)
    have he : paperQuadrilateralSideNeighbor 0 = (paperTraceFreeGroupBasis 0)⁻¹ := by
      apply Subtype.ext
      change paperGeneratorASL⁻¹ = (paperTraceFreeGroupBasis 0 : SL(2, ℤ))⁻¹
      rw [paperTraceFreeGroupBasis_zero]
    rw [he, map_inv, paperTraceAbelianizationCoordinates_basis_zero]
    rfl
  · change paperTraceAbelianizationCoordinates (paperQuadrilateralSideNeighbor 1) =
      Multiplicative.ofAdd ((0, -1) : ℤ × ℤ)
    have he : paperQuadrilateralSideNeighbor 1 = (paperTraceFreeGroupBasis 1)⁻¹ := by
      apply Subtype.ext
      change paperGeneratorBSL⁻¹ = (paperTraceFreeGroupBasis 1 : SL(2, ℤ))⁻¹
      rw [paperTraceFreeGroupBasis_one]
    rw [he, map_inv, paperTraceAbelianizationCoordinates_basis_one]
    rfl
  · change paperTraceAbelianizationCoordinates (paperQuadrilateralSideNeighbor 2) =
      Multiplicative.ofAdd ((1, 0) : ℤ × ℤ)
    have he : paperQuadrilateralSideNeighbor 2 = paperTraceFreeGroupBasis 0 := by
      apply Subtype.ext
      exact paperTraceFreeGroupBasis_zero.symm
    rw [he, paperTraceAbelianizationCoordinates_basis_zero]
  · change paperTraceAbelianizationCoordinates (paperQuadrilateralSideNeighbor 3) =
      Multiplicative.ofAdd ((0, 1) : ℤ × ℤ)
    have he : paperQuadrilateralSideNeighbor 3 = paperTraceFreeGroupBasis 1 := by
      apply Subtype.ext
      exact paperTraceFreeGroupBasis_one.symm
    rw [he, paperTraceAbelianizationCoordinates_basis_one]

private theorem wordH1_coordinates_sum (w : List (Fin 4)) :
    (paperTraceAbelianizationCoordinates ((w.map paperQuadrilateralSideNeighbor).prod)).toAdd =
      (w.map paperAxisCellLetterCoordinates).sum := by
  induction w with
  | nil =>
      rw [List.map_nil, List.prod_nil, map_one, List.map_nil, List.sum_nil]
      rfl
  | cons k w ih =>
      rw [List.map_cons, List.prod_cons, map_mul, paperQuadrilateralSideNeighbor_coordinates,
        List.map_cons, List.sum_cons]
      change paperAxisCellLetterCoordinates k +
          (paperTraceAbelianizationCoordinates ((w.map paperQuadrilateralSideNeighbor).prod)).toAdd = _
      rw [ih]

/-- The signed letter sum of the actual constructed ordered word is exactly
the actual deck element's original A/B coordinates; conjugation cancels only
after applying the genuine abelianization homomorphism. -/
theorem paperAxisPeriodCellWord_signedSum
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) :
    ((paperAxisPeriodCellWord g hg a).map paperAxisCellLetterCoordinates).sum =
      (paperTraceAbelianizationCoordinates g).toAdd := by
  rw [← wordH1_coordinates_sum, paperAxisPeriodCellWord_prod g hg a ha,
    map_mul paperTraceAbelianizationCoordinates, map_mul paperTraceAbelianizationCoordinates,
    map_inv paperTraceAbelianizationCoordinates]
  change -(paperTraceAbelianizationCoordinates
      (paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a))).toAdd +
      (paperTraceAbelianizationCoordinates g).toAdd +
      (paperTraceAbelianizationCoordinates
        (paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a))).toAdd = _
  abel

/-- The literal side-word signed sum is the genuine fixed-I singular-H1
marking of the actual oriented full-period geodesic loop. -/
theorem paperAxisPeriodCellWord_fixedSingularCoordinates
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) :
    ((paperAxisPeriodCellWord g hg a).map paperAxisCellLetterCoordinates).sum =
      modularTraceFixedSingularH1Equiv
        (singularLoopClass ModularTraceQuotient (modularClosedGeodesicLoop g hg)) := by
  rw [paperAxisPeriodCellWord_signedSum g hg a ha,
    modularClosedGeodesicLoop_fixedSingularCoordinates]

end Markov
