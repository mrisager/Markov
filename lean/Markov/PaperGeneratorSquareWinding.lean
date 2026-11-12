import Markov.PaperActualPuncturedTorus
import Markov.ModularH1Transport
import Markov.NormalizedCircleWinding

noncomputable section
open Set Topology
open scoped MatrixGroups
namespace Markov

/-- The normalized source and target of the original positive A side pairing. -/
def paperSquareAStart : paperPuncturedSquare := ⟨(0, 1), by norm_num [paperPuncturedSquare]⟩
def paperSquareAEnd : paperPuncturedSquare := ⟨(0, -1), by norm_num [paperPuncturedSquare]⟩
/-- The normalized source and target of the original positive B side pairing. -/
def paperSquareBStart : paperPuncturedSquare := ⟨(1, 0), by norm_num [paperPuncturedSquare]⟩
def paperSquareBEnd : paperPuncturedSquare := ⟨(-1, 0), by norm_num [paperPuncturedSquare]⟩

/-- The literal downward center line, with the punctured-square topology. -/
def paperSquareAPath : Path paperSquareAStart paperSquareAEnd where
  toFun t := ⟨(0, 1 - 2 * (t : ℝ)), by
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    have hy : |1 - 2 * (t : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    refine ⟨by norm_num, hy, ?_⟩
    have hsq := paperSquare_coord_sq_le_one hy
    dsimp
    nlinarith⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; norm_num [paperSquareAStart]
  target' := by apply Subtype.ext; norm_num [paperSquareAEnd]

/-- The literal leftward center line, with the punctured-square topology. -/
def paperSquareBPath : Path paperSquareBStart paperSquareBEnd where
  toFun t := ⟨(1 - 2 * (t : ℝ), 0), by
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    have hx : |1 - 2 * (t : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    refine ⟨hx, by norm_num, ?_⟩
    have hsq := paperSquare_coord_sq_le_one hx
    dsimp
    nlinarith⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; norm_num [paperSquareBStart]
  target' := by apply Subtype.ext; norm_num [paperSquareBEnd]

/-- The inverse actual marked chart takes the downward endpoints to literal A-related points. -/
theorem paperSquareAEnd_actual_action :
    paperGeneratorASL • (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareAStart).val =
      (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareAEnd).val := by
  apply ((paperMarkedSquare_A_pair_iff _ _).mp ?_).2
  simp only [Homeomorph.apply_symm_apply]
  exact ⟨rfl, rfl, rfl⟩

/-- The inverse actual marked chart takes the leftward endpoints to literal B-related points. -/
theorem paperSquareBEnd_actual_action :
    paperGeneratorBSL • (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareBStart).val =
      (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareBEnd).val := by
  apply ((paperMarkedSquare_B_pair_iff _ _).mp ?_).2
  simp only [Homeomorph.apply_symm_apply]
  exact ⟨rfl, rfl, rfl⟩

/-- An actual upper-half-plane path to the positive original A deck translate. -/
def paperSquareALiftedPath : Path
    (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareAStart).val
    ((paperTraceFreeGroupBasis 0) •
      (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareAStart).val) :=
  ((paperSquareAPath.map paperMarkedQuadrilateralSquareHomeomorph.symm.continuous).map
    continuous_subtype_val).cast rfl (by
      change (paperTraceFreeGroupBasis 0 : SL(2, ℤ)) •
        (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareAStart).val =
        (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareAEnd).val
      rw [paperTraceFreeGroupBasis_zero]
      exact paperSquareAEnd_actual_action)

/-- An actual upper-half-plane path to the positive original B deck translate. -/
def paperSquareBLiftedPath : Path
    (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareBStart).val
    ((paperTraceFreeGroupBasis 1) •
      (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareBStart).val) :=
  ((paperSquareBPath.map paperMarkedQuadrilateralSquareHomeomorph.symm.continuous).map
    continuous_subtype_val).cast rfl (by
      change (paperTraceFreeGroupBasis 1 : SL(2, ℤ)) •
        (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareBStart).val =
        (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareBEnd).val
      rw [paperTraceFreeGroupBasis_one]
      exact paperSquareBEnd_actual_action)

/-- The explicit normalized-center positive original A loop in the actual quotient. -/
def paperSquareAOriginalLoop : Path
    (modularTraceQuotientMk (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareAStart).val)
    (modularTraceQuotientMk (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareAStart).val) :=
  (paperSquareALiftedPath.map modularTraceQuotientMk_continuous).cast rfl
    (modularTraceQuotientMk_smul (paperTraceFreeGroupBasis 0) _).symm

/-- The explicit normalized-center positive original B loop in the actual quotient. -/
def paperSquareBOriginalLoop : Path
    (modularTraceQuotientMk (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareBStart).val)
    (modularTraceQuotientMk (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareBStart).val) :=
  (paperSquareBLiftedPath.map modularTraceQuotientMk_continuous).cast rfl
    (modularTraceQuotientMk_smul (paperTraceFreeGroupBasis 1) _).symm

/-- The actual fixed-I H1 marking of the displayed original A loop. -/
theorem paperSquareAOriginalLoop_fixedH1 :
    modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient paperSquareAOriginalLoop) = ((1, 0) : ℤ × ℤ) := by
  unfold paperSquareAOriginalLoop
  rw [modularTraceFixedSingularH1Equiv_projectedPath,
    paperTraceAbelianizationCoordinates_basis_zero]
  rfl

/-- The actual fixed-I H1 marking of the displayed original B loop. -/
theorem paperSquareBOriginalLoop_fixedH1 :
    modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient paperSquareBOriginalLoop) = ((0, 1) : ℤ × ℤ) := by
  unfold paperSquareBOriginalLoop
  rw [modularTraceFixedSingularH1Equiv_projectedPath,
    paperTraceAbelianizationCoordinates_basis_one]
  rfl

/-- Exact pointwise image of the actual original A loop under the actual torus homeomorphism. -/
theorem paperSquareAOriginalLoop_standard (t : unitInterval) :
    modularTraceQuotientPuncturedTorusHomeomorph (paperSquareAOriginalLoop t) =
      standardPuncturedTorusMap (paperSquareAPath t) := by
  change modularTraceQuotientPuncturedTorusHomeomorph
    (modularTraceQuotientMk
      (paperMarkedQuadrilateralSquareHomeomorph.symm (paperSquareAPath t)).val) = _
  rw [modularTraceQuotientPuncturedTorusHomeomorph_mk, Homeomorph.apply_symm_apply]

/-- Exact pointwise image of the actual original B loop under the actual torus homeomorphism. -/
theorem paperSquareBOriginalLoop_standard (t : unitInterval) :
    modularTraceQuotientPuncturedTorusHomeomorph (paperSquareBOriginalLoop t) =
      standardPuncturedTorusMap (paperSquareBPath t) := by
  change modularTraceQuotientPuncturedTorusHomeomorph
    (modularTraceQuotientMk
      (paperMarkedQuadrilateralSquareHomeomorph.symm (paperSquareBPath t)).val) = _
  rw [modularTraceQuotientPuncturedTorusHomeomorph_mk, Homeomorph.apply_symm_apply]

/-- Each circle coordinate is translated to zero before taking winding. -/
def standardTorusFirstCoordinateLoop {x : StandardPuncturedTorus} (γ : Path x x) :
    Path (0 : NormalizedCircle) 0 where
  toFun t := (γ t).val.1 - x.val.1
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

def standardTorusSecondCoordinateLoop {x : StandardPuncturedTorus} (γ : Path x x) :
    Path (0 : NormalizedCircle) 0 where
  toFun t := (γ t).val.2 - x.val.2
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- Concrete winding labels of a standard-torus loop; this definition asserts no homology naturality. -/
def standardTorusLoopWinding {x : StandardPuncturedTorus} (γ : Path x x) : ℤ × ℤ :=
  (normalizedCircleWinding (standardTorusFirstCoordinateLoop γ),
    normalizedCircleWinding (standardTorusSecondCoordinateLoop γ))

/-- The actual mapped original A loop. -/
def paperSquareAMappedLoop :=
  paperSquareAOriginalLoop.map modularTraceQuotientPuncturedTorusHomeomorph.continuous

/-- The actual mapped original B loop. -/
def paperSquareBMappedLoop :=
  paperSquareBOriginalLoop.map modularTraceQuotientPuncturedTorusHomeomorph.continuous

/-- Its first translated coordinate is literally the zero-winding projected segment. -/
theorem paperSquareAMappedLoop_firstCoordinate :
    standardTorusFirstCoordinateLoop paperSquareAMappedLoop = normalizedCircleIntegerLoop 0 := by
  ext t
  change (modularTraceQuotientPuncturedTorusHomeomorph (paperSquareAOriginalLoop t)).val.1 -
    (modularTraceQuotientPuncturedTorusHomeomorph
      (modularTraceQuotientMk (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareAStart).val)).val.1 = _
  rw [paperSquareAOriginalLoop_standard, modularTraceQuotientPuncturedTorusHomeomorph_mk,
    Homeomorph.apply_symm_apply]
  rw [standardPuncturedTorusMap_coe, standardPuncturedTorusMap_coe]
  change standardCircleSquareScalar 0 - standardCircleSquareScalar 0 = normalizedCircleIntegerLoop 0 t
  rw [sub_self, normalizedCircleIntegerLoop_apply]
  norm_num

/-- Its second translated coordinate is literally the negative once-around loop. -/
theorem paperSquareAMappedLoop_secondCoordinate :
    standardTorusSecondCoordinateLoop paperSquareAMappedLoop = normalizedCircleIntegerLoop (-1) := by
  ext t
  change (modularTraceQuotientPuncturedTorusHomeomorph (paperSquareAOriginalLoop t)).val.2 -
    (modularTraceQuotientPuncturedTorusHomeomorph
      (modularTraceQuotientMk (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareAStart).val)).val.2 = _
  rw [paperSquareAOriginalLoop_standard, modularTraceQuotientPuncturedTorusHomeomorph_mk,
    Homeomorph.apply_symm_apply]
  rw [standardPuncturedTorusMap_coe, standardPuncturedTorusMap_coe]
  change standardCircleSquareScalar (1 - 2 * (t : ℝ)) - standardCircleSquareScalar 1 =
    normalizedCircleIntegerLoop (-1) t
  rw [standardCircleSquareScalar_one, sub_zero, normalizedCircleIntegerLoop_apply]
  simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one]
  change (((1 - 2 * (t : ℝ) + 1) / 2 : ℝ) : NormalizedCircle) = ((-(t : ℝ) : ℝ) : NormalizedCircle)
  have he : (1 - 2 * (t : ℝ) + 1) / 2 = 1 + -(t : ℝ) := by ring
  rw [he, AddCircle.coe_add, AddCircle.coe_period, zero_add]

/-- Its first translated coordinate is literally the negative once-around loop. -/
theorem paperSquareBMappedLoop_firstCoordinate :
    standardTorusFirstCoordinateLoop paperSquareBMappedLoop = normalizedCircleIntegerLoop (-1) := by
  ext t
  change (modularTraceQuotientPuncturedTorusHomeomorph (paperSquareBOriginalLoop t)).val.1 -
    (modularTraceQuotientPuncturedTorusHomeomorph
      (modularTraceQuotientMk (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareBStart).val)).val.1 = _
  rw [paperSquareBOriginalLoop_standard, modularTraceQuotientPuncturedTorusHomeomorph_mk,
    Homeomorph.apply_symm_apply]
  rw [standardPuncturedTorusMap_coe, standardPuncturedTorusMap_coe]
  change standardCircleSquareScalar (1 - 2 * (t : ℝ)) - standardCircleSquareScalar 1 =
    normalizedCircleIntegerLoop (-1) t
  rw [standardCircleSquareScalar_one, sub_zero, normalizedCircleIntegerLoop_apply]
  simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one]
  change (((1 - 2 * (t : ℝ) + 1) / 2 : ℝ) : NormalizedCircle) = ((-(t : ℝ) : ℝ) : NormalizedCircle)
  have he : (1 - 2 * (t : ℝ) + 1) / 2 = 1 + -(t : ℝ) := by ring
  rw [he, AddCircle.coe_add, AddCircle.coe_period, zero_add]

/-- Its second translated coordinate is literally the zero-winding projected segment. -/
theorem paperSquareBMappedLoop_secondCoordinate :
    standardTorusSecondCoordinateLoop paperSquareBMappedLoop = normalizedCircleIntegerLoop 0 := by
  ext t
  change (modularTraceQuotientPuncturedTorusHomeomorph (paperSquareBOriginalLoop t)).val.2 -
    (modularTraceQuotientPuncturedTorusHomeomorph
      (modularTraceQuotientMk (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareBStart).val)).val.2 = _
  rw [paperSquareBOriginalLoop_standard, modularTraceQuotientPuncturedTorusHomeomorph_mk,
    Homeomorph.apply_symm_apply]
  rw [standardPuncturedTorusMap_coe, standardPuncturedTorusMap_coe]
  change standardCircleSquareScalar 0 - standardCircleSquareScalar 0 = normalizedCircleIntegerLoop 0 t
  rw [sub_self, normalizedCircleIntegerLoop_apply]
  norm_num

/-- Positive original A maps to standard winding (0,-1). -/
theorem paperSquareAOriginalLoop_standardWinding :
    standardTorusLoopWinding paperSquareAMappedLoop = ((0, -1) : ℤ × ℤ) := by
  unfold standardTorusLoopWinding
  rw [paperSquareAMappedLoop_firstCoordinate, paperSquareAMappedLoop_secondCoordinate,
    normalizedCircleWinding_integerLoop, normalizedCircleWinding_integerLoop]

/-- Positive original B maps to standard winding (-1,0). -/
theorem paperSquareBOriginalLoop_standardWinding :
    standardTorusLoopWinding paperSquareBMappedLoop = ((-1, 0) : ℤ × ℤ) := by
  unfold standardTorusLoopWinding
  rw [paperSquareBMappedLoop_firstCoordinate, paperSquareBMappedLoop_secondCoordinate,
    normalizedCircleWinding_integerLoop, normalizedCircleWinding_integerLoop]

end Markov
