import Markov.PaperAxisCellWordH1
import Markov.PaperSimpleGeneratorCalibration

/-! The actual normalized phase-period lift has the literal ordered cell-word
endpoint. Its projection gives a genuine quotient loop, with full nonabelian
marking and fixed-I singular H1. Marking reverses the side-letter evaluation;
no noncommutative whole-word action is inferred from H1. -/
noncomputable section
open Set Topology
open scoped MatrixGroups
namespace Markov

/-- The actual phase point normalized by the actual first itinerary label. -/
def paperAxisCellWordBase (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) : UpperHalfPlane :=
  (paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a))⁻¹ •
    modularHyperbolicAxis g hg a

/-- A genuine lifted phase-period path to the literal evaluated word endpoint. -/
def paperAxisCellWordLift (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) :
    Path (paperAxisCellWordBase g hg a)
      (((paperAxisPeriodCellWord g hg a).map paperQuadrilateralSideNeighbor).prod •
        paperAxisCellWordBase g hg a) where
  toFun t := (paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a))⁻¹ •
    modularHyperbolicAxis g hg (a + (t : ℝ) * modularClosedGeodesicPeriod g)
  continuous_toFun :=
    (modularSubgroup_isometry modularTraceSubgroup
      (paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a))⁻¹).continuous.comp
        ((modularHyperbolicAxis_isometry g hg).continuous.comp
          (continuous_const.add (continuous_subtype_val.mul continuous_const)))
  source' := by
    change _ • modularHyperbolicAxis g hg (a + (0 : ℝ) * modularClosedGeodesicPeriod g) = _
    simp only [zero_mul, add_zero]
    rfl
  target' := by
    change _ • modularHyperbolicAxis g hg (a + (1 : ℝ) * modularClosedGeodesicPeriod g) = _
    rw [one_mul, paperAxisPeriodCellWord_prod g hg a ha, ← modularHyperbolicAxis_action g hg a]
    simp only [paperAxisCellWordBase, mul_smul, smul_inv_smul]

/-- The projection of that actual lifted path, with its actual orbit endpoint
cast, is a genuine based loop in the actual quotient. -/
def paperAxisCellWordProjectedLoop (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) :
    Path (modularTraceQuotientMk (paperAxisCellWordBase g hg a))
      (modularTraceQuotientMk (paperAxisCellWordBase g hg a)) :=
  ((paperAxisCellWordLift g hg a ha).map modularTraceQuotientMk_continuous).cast rfl
    (modularTraceQuotientMk_smul
      ((paperAxisPeriodCellWord g hg a).map paperQuadrilateralSideNeighbor).prod
      (paperAxisCellWordBase g hg a)).symm

/-- Pointwise this is exactly the forward actual projected axis period at
the chosen real phase, with the original parameter orientation. -/
theorem paperAxisCellWordProjectedLoop_apply
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : unitInterval) :
    paperAxisCellWordProjectedLoop g hg a ha t =
      modularClosedGeodesic g hg (a + (t : ℝ) * modularClosedGeodesicPeriod g) := by
  change modularTraceQuotientMk
      ((paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a))⁻¹ •
        modularHyperbolicAxis g hg (a + (t : ℝ) * modularClosedGeodesicPeriod g)) = _
  exact modularTraceQuotientMk_smul _ _

/-- The exact genuine nonabelian marking keeps the actual whole-word inverse
and actual S-conjugation; neither is replaced by an abelianized inference. -/
theorem paperAxisCellWordProjectedLoop_marked
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) :
    modularTraceMarkedFundamentalGroupEquiv (paperAxisCellWordBase g hg a)
      (FundamentalGroup.fromPath (.mk (paperAxisCellWordProjectedLoop g hg a ha))) =
      modularTraceSeedConjugation
        (((paperAxisPeriodCellWord g hg a).map paperQuadrilateralSideNeighbor).prod)⁻¹ :=
  modularTraceMarkedFundamentalGroupEquiv_projectedPath (paperAxisCellWordBase g hg a)
    ((paperAxisPeriodCellWord g hg a).map paperQuadrilateralSideNeighbor).prod
    (paperAxisCellWordLift g hg a ha)

private theorem wordLoop_seed_inverse_letter (k : Fin 4) :
    modularTraceSeedConjugation (paperQuadrilateralSideNeighbor k)⁻¹ =
      paperQuadrilateralSideNeighbor k := by
  fin_cases k
  · change modularTraceSeedConjugation (paperQuadrilateralSideNeighbor 0)⁻¹ =
      paperQuadrilateralSideNeighbor 0
    have he : paperQuadrilateralSideNeighbor 0 = (paperTraceFreeGroupBasis 0)⁻¹ := by
      apply Subtype.ext
      change paperGeneratorASL⁻¹ = (paperTraceFreeGroupBasis 0 : SL(2, ℤ))⁻¹
      rw [paperTraceFreeGroupBasis_zero]
    rw [he, inv_inv, modularTraceSeedConjugation_basis]
  · change modularTraceSeedConjugation (paperQuadrilateralSideNeighbor 1)⁻¹ =
      paperQuadrilateralSideNeighbor 1
    have he : paperQuadrilateralSideNeighbor 1 = (paperTraceFreeGroupBasis 1)⁻¹ := by
      apply Subtype.ext
      change paperGeneratorBSL⁻¹ = (paperTraceFreeGroupBasis 1 : SL(2, ℤ))⁻¹
      rw [paperTraceFreeGroupBasis_one]
    rw [he, inv_inv, modularTraceSeedConjugation_basis]
  · change modularTraceSeedConjugation (paperQuadrilateralSideNeighbor 2)⁻¹ =
      paperQuadrilateralSideNeighbor 2
    have he : paperQuadrilateralSideNeighbor 2 = paperTraceFreeGroupBasis 0 :=
      Subtype.ext paperTraceFreeGroupBasis_zero.symm
    rw [he, modularTraceSeedConjugation_inv_basis]
  · change modularTraceSeedConjugation (paperQuadrilateralSideNeighbor 3)⁻¹ =
      paperQuadrilateralSideNeighbor 3
    have he : paperQuadrilateralSideNeighbor 3 = paperTraceFreeGroupBasis 1 :=
      Subtype.ext paperTraceFreeGroupBasis_one.symm
    rw [he, modularTraceSeedConjugation_inv_basis]

private theorem wordLoop_seed_inverse_reverse (w : List (Fin 4)) :
    modularTraceSeedConjugation ((w.map paperQuadrilateralSideNeighbor).prod)⁻¹ =
      (w.reverse.map paperQuadrilateralSideNeighbor).prod := by
  induction w with
  | nil => simp only [List.map_nil, List.prod_nil, inv_one, map_one, List.reverse_nil]
  | cons k w ih =>
      rw [List.map_cons, List.prod_cons, mul_inv_rev, map_mul, ih, wordLoop_seed_inverse_letter,
        List.reverse_cons, List.map_append, List.prod_append, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]

/-- In the calibrated original marking the actual forward loop evaluates the
REVERSED side-letter list. The reversal is a proved nonabelian orientation fact. -/
theorem paperAxisCellWordProjectedLoop_marked_reverseWord
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) :
    modularTraceMarkedFundamentalGroupEquiv (paperAxisCellWordBase g hg a)
      (FundamentalGroup.fromPath (.mk (paperAxisCellWordProjectedLoop g hg a ha))) =
      ((paperAxisPeriodCellWord g hg a).reverse.map paperQuadrilateralSideNeighbor).prod := by
  rw [paperAxisCellWordProjectedLoop_marked]
  exact wordLoop_seed_inverse_reverse _

/-- The genuine fixed-I singular class of the actual projected phase-period
loop equals the signed sum of the actual side word, with no H1-to-pi1 inference. -/
theorem paperAxisCellWordProjectedLoop_fixedSingularCoordinates
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) :
    modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient (paperAxisCellWordProjectedLoop g hg a ha)) =
      ((paperAxisPeriodCellWord g hg a).map paperAxisCellLetterCoordinates).sum := by
  rw [paperAxisCellWordProjectedLoop, modularTraceFixedSingularH1Equiv_projectedPath,
    paperAxisPeriodCellWord_prod g hg a ha, map_mul paperTraceAbelianizationCoordinates,
    map_mul paperTraceAbelianizationCoordinates, map_inv paperTraceAbelianizationCoordinates,
    paperAxisPeriodCellWord_signedSum g hg a ha]
  change -(paperTraceAbelianizationCoordinates
      (paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a))).toAdd +
      (paperTraceAbelianizationCoordinates g).toAdd +
      (paperTraceAbelianizationCoordinates
        (paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a))).toAdd = _
  abel

end Markov
