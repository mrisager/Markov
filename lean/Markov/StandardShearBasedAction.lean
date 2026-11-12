import Markov.UnimodularTorusHomeomorphisms
import Markov.StandardShearSurgery
import Markov.NormalizedCircleWindingConjugation

/-! Actual based path action of the determinant-one column shear. All results
retain path traversal order and explicit connector/basepoint casts. -/

noncomputable section
open Topology
namespace Markov

/-- The actual column shear (x,y)↦(x+y,y) on the actual punctured torus. -/
def surgeryColumnShear : StandardPuncturedTorus ≃ₜ StandardPuncturedTorus :=
  standardUnimodularPuncturedTorusHomeomorph (1,0) (1,1) (by norm_num [intDet])

@[simp] theorem surgeryColumnShear_coe (z : StandardPuncturedTorus) :
    (surgeryColumnShear z).val = (z.val.1 + z.val.2, z.val.2) := by
  change ((1 : ℤ) • z.val.1 + (1 : ℤ) • z.val.2,
    (0 : ℤ) • z.val.1 + (1 : ℤ) • z.val.2) = _
  simp

/-- The frozen actual horizontal connector ends at exactly the sheared basepoint. -/
theorem surgeryColumnShear_base : surgeryColumnShear surgeryBasePoint =
    shearSurgeryDiagonalBasePoint := by
  apply Subtype.ext
  rw [surgeryColumnShear_coe]
  apply Prod.ext
  · change (((1/2 : ℝ) : NormalizedCircle) + ((1/2 : ℝ) : NormalizedCircle)) =
      ((1 : ℝ) : NormalizedCircle)
    change ((1/2+1/2 : ℝ) : NormalizedCircle) = ((1 : ℝ) : NormalizedCircle)
    norm_num
  · rfl

/-- The actual sheared horizontal loop with its actual equal basepoint displayed literally. -/
def surgeryShearMappedHorizontal : Path shearSurgeryDiagonalBasePoint shearSurgeryDiagonalBasePoint :=
  (surgeryHorizontalLoop.map surgeryColumnShear.continuous).cast
    surgeryColumnShear_base.symm surgeryColumnShear_base.symm

/-- The actual sheared vertical loop with the same explicit basepoint cast. -/
def surgeryShearMappedVertical : Path shearSurgeryDiagonalBasePoint shearSurgeryDiagonalBasePoint :=
  (surgeryVerticalLoop.map surgeryColumnShear.continuous).cast
    surgeryColumnShear_base.symm surgeryColumnShear_base.symm

private theorem horizontal_lift_formula (t : unitInterval) :
    surgeryHorizontalLift t = (1/2+(t : ℝ), 1/2) := by
  simp [surgeryHorizontalLift, Path.segment_apply, AffineMap.lineMap_apply_module,
    surgeryBaseLift, surgeryMiddleLift]
  constructor <;> ring

private theorem vertical_lift_formula (t : unitInterval) :
    surgeryVerticalLift t = (3/2, 1/2+(t : ℝ)) := by
  simp [surgeryVerticalLift, Path.segment_apply, AffineMap.lineMap_apply_module,
    surgeryMiddleLift, surgeryEndLift]
  constructor <;> ring

private theorem diagonal_lift_formula (t : unitInterval) :
    shearSurgeryDiagonalLift t = (1+(t : ℝ), 1/2+(t : ℝ)) := by
  simp [shearSurgeryDiagonalLift, Path.segment_apply, AffineMap.lineMap_apply_module,
    shearSurgeryDiagonalStartLift, shearSurgeryDiagonalEndLift]
  constructor <;> ring

private theorem connector_lift_formula (t : unitInterval) :
    shearSurgeryConnectorLift t = (1/2+(t : ℝ)/2, 1/2) := by
  simp [shearSurgeryConnectorLift, Path.segment_apply, AffineMap.lineMap_apply_module,
    surgeryBaseLift, shearSurgeryDiagonalStartLift]
  constructor <;> ring

/-- The sheared vertical loop is literally the frozen actual embedded diagonal loop. -/
theorem surgeryShearMappedVertical_eq_diagonal : surgeryShearMappedVertical =
    shearSurgeryDiagonalLoop := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change (surgeryColumnShear (surgeryVerticalLoop t)).val =
    surgeryPlaneProjection (shearSurgeryDiagonalLift t)
  rw [surgeryColumnShear_coe]
  change (((surgeryPlaneProjection (surgeryVerticalLift t)).1 +
    (surgeryPlaneProjection (surgeryVerticalLift t)).2),
    (surgeryPlaneProjection (surgeryVerticalLift t)).2) = _
  rw [vertical_lift_formula, diagonal_lift_formula]
  apply Prod.ext
  · change (((3/2 : ℝ) : NormalizedCircle) + (((1/2+(t : ℝ) : ℝ)) : NormalizedCircle)) =
      (((1+(t : ℝ) : ℝ)) : NormalizedCircle)
    change (((3/2+(1/2+(t : ℝ)) : ℝ)) : NormalizedCircle) =
      (((1+(t : ℝ) : ℝ)) : NormalizedCircle)
    have h : 3/2+(1/2+(t : ℝ)) = (1+(t : ℝ))+1 := by ring
    rw [h, AddCircle.coe_add_period]
  · rfl

/-- The sheared horizontal loop brought back to the original basepoint by the explicit connector. -/
def surgeryShearHorizontalBasedLoop : Path surgeryBasePoint surgeryBasePoint :=
  (shearSurgeryConnector.trans surgeryShearMappedHorizontal).trans shearSurgeryConnector.symm

/-- The sheared vertical loop brought back by the same actual connector. -/
def surgeryShearVerticalBasedLoop : Path surgeryBasePoint surgeryBasePoint :=
  (shearSurgeryConnector.trans surgeryShearMappedVertical).trans shearSurgeryConnector.symm

/-- Actual vertical image in positive path traversal order, without translating to a group word. -/
theorem surgeryShearVerticalBasedLoop_homotopic :
    surgeryShearVerticalBasedLoop.Homotopic (surgeryHorizontalLoop.trans surgeryVerticalLoop) := by
  unfold surgeryShearVerticalBasedLoop
  rw [surgeryShearMappedVertical_eq_diagonal]
  exact shearSurgeryPositiveProduct_homotopic_embeddedDiagonal.symm

private def horizontalSlice (z : NormalizedCircle) : StandardPuncturedTorus :=
  ⟨(z + standardCircleHalf, standardCircleHalf), by
    intro h
    exact standardCircleHalf_ne_zero (congrArg Prod.snd h)⟩

private theorem horizontalSlice_continuous : Continuous horizontalSlice := by
  unfold horizontalSlice
  fun_prop

private theorem horizontalSlice_zero : horizontalSlice 0 = surgeryBasePoint := by
  apply Subtype.ext
  apply Prod.ext
  · change (0 : NormalizedCircle) + standardCircleHalf = standardCircleHalf
    exact zero_add _
  · rfl

private theorem first_coordinate_continuous :
    Continuous (fun z : StandardPuncturedTorus => z.val.1) :=
  continuous_fst.comp continuous_subtype_val

private theorem horizontal_loop_homotopic_of_winding
    (γ δ : Path surgeryBasePoint surgeryBasePoint)
    (hγ : ∀ t, (γ t).val.2 = standardCircleHalf)
    (hδ : ∀ t, (δ t).val.2 = standardCircleHalf)
    (hw : normalizedCircleWinding (normalizedCircleTranslatedLoop (γ.map first_coordinate_continuous)) =
      normalizedCircleWinding (normalizedCircleTranslatedLoop (δ.map first_coordinate_continuous))) :
    γ.Homotopic δ := by
  have h := (normalizedCircleWinding_homotopic_iff _ _).mp hw
  have hm := (h.map ⟨horizontalSlice, horizontalSlice_continuous⟩).pathCast
    horizontalSlice_zero.symm horizontalSlice_zero.symm
  have hγ' : ((normalizedCircleTranslatedLoop (γ.map first_coordinate_continuous)).map
      horizontalSlice_continuous).cast horizontalSlice_zero.symm horizontalSlice_zero.symm = γ := by
    apply Path.ext
    funext t
    apply Subtype.ext
    apply Prod.ext
    · change ((γ t).val.1 - standardCircleHalf) + standardCircleHalf = (γ t).val.1
      exact sub_add_cancel _ _
    · exact (hγ t).symm
  have hδ' : ((normalizedCircleTranslatedLoop (δ.map first_coordinate_continuous)).map
      horizontalSlice_continuous).cast horizontalSlice_zero.symm horizontalSlice_zero.symm = δ := by
    apply Path.ext
    funext t
    apply Subtype.ext
    apply Prod.ext
    · change ((δ t).val.1 - standardCircleHalf) + standardCircleHalf = (δ t).val.1
      exact sub_add_cancel _ _
    · exact (hδ t).symm
  rwa [hγ', hδ'] at hm

private theorem horizontal_second (t : unitInterval) :
    (surgeryHorizontalLoop t).val.2 = standardCircleHalf := by
  change (surgeryPlaneProjection (surgeryHorizontalLift t)).2 = standardCircleHalf
  rw [horizontal_lift_formula]
  rfl

private theorem connector_second (t : unitInterval) :
    (shearSurgeryConnector t).val.2 = standardCircleHalf := by
  change (surgeryPlaneProjection (shearSurgeryConnectorLift t)).2 = standardCircleHalf
  rw [connector_lift_formula]
  rfl

private theorem mapped_horizontal_second (t : unitInterval) :
    (surgeryShearMappedHorizontal t).val.2 = standardCircleHalf := by
  change (surgeryColumnShear (surgeryHorizontalLoop t)).val.2 = standardCircleHalf
  rw [surgeryColumnShear_coe]
  exact horizontal_second t

private theorem horizontal_trans {a b c : StandardPuncturedTorus}
    (α : Path a b) (γ : Path b c)
    (hα : ∀ t, (α t).val.2 = standardCircleHalf)
    (hγ : ∀ t, (γ t).val.2 = standardCircleHalf) :
    ∀ t, ((α.trans γ) t).val.2 = standardCircleHalf := by
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact hα _
  · exact hγ _

private theorem based_horizontal_second (t : unitInterval) :
    (surgeryShearHorizontalBasedLoop t).val.2 = standardCircleHalf := by
  exact horizontal_trans _ _
    (horizontal_trans _ _ connector_second mapped_horizontal_second)
    (fun u => connector_second (unitInterval.symm u)) t

private theorem horizontal_translated_eq_standard :
    normalizedCircleTranslatedLoop (surgeryHorizontalLoop.map first_coordinate_continuous) =
      normalizedCircleStandardLoop := by
  apply Path.ext
  funext t
  change (surgeryPlaneProjection (surgeryHorizontalLift t)).1 - standardCircleHalf =
    normalizedCircleStandardLoop t
  rw [horizontal_lift_formula, normalizedCircleStandardLoop_apply]
  change (standardCircleHalf + ((t : ℝ) : NormalizedCircle)) - standardCircleHalf =
    ((t : ℝ) : NormalizedCircle)
  abel

private theorem mapped_horizontal_translated_eq_standard :
    normalizedCircleTranslatedLoop (surgeryShearMappedHorizontal.map first_coordinate_continuous) =
      normalizedCircleStandardLoop := by
  apply Path.ext
  funext t
  change (surgeryColumnShear (surgeryHorizontalLoop t)).val.1 -
    shearSurgeryDiagonalBasePoint.val.1 = normalizedCircleStandardLoop t
  rw [surgeryColumnShear_coe, normalizedCircleStandardLoop_apply]
  change ((surgeryPlaneProjection (surgeryHorizontalLift t)).1 +
    (surgeryPlaneProjection (surgeryHorizontalLift t)).2) - ((1 : ℝ) : NormalizedCircle) = _
  rw [horizontal_lift_formula]
  have hh : standardCircleHalf + standardCircleHalf = ((1 : ℝ) : NormalizedCircle) := by
    change ((1/2+1/2 : ℝ) : NormalizedCircle) = ((1 : ℝ) : NormalizedCircle)
    norm_num
  rw [← hh]
  change (standardCircleHalf + ((t : ℝ) : NormalizedCircle) + standardCircleHalf) -
    (standardCircleHalf + standardCircleHalf) = ((t : ℝ) : NormalizedCircle)
  abel

private theorem based_horizontal_winding :
    normalizedCircleWinding
      (normalizedCircleTranslatedLoop (surgeryShearHorizontalBasedLoop.map first_coordinate_continuous)) = 1 := by
  change normalizedCircleWinding (normalizedCircleTranslatedLoop
    (((shearSurgeryConnector.trans surgeryShearMappedHorizontal).trans shearSurgeryConnector.symm).map
      first_coordinate_continuous)) = 1
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm,
    normalizedCircleWinding_translated_conjugate, mapped_horizontal_translated_eq_standard,
    normalizedCircleWinding_standardLoop]

/-- Actual horizontal image: the same explicit basepoint connector preserves
the genuine homotopy class of the positive horizontal loop. -/
theorem surgeryShearHorizontalBasedLoop_homotopic :
    surgeryShearHorizontalBasedLoop.Homotopic surgeryHorizontalLoop := by
  apply horizontal_loop_homotopic_of_winding _ _ based_horizontal_second horizontal_second
  rw [based_horizontal_winding, horizontal_translated_eq_standard,
    normalizedCircleWinding_standardLoop]

end Markov
