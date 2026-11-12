import Markov.StandardShearBasedAction
import Markov.SignedSwapTorusHomeomorphisms
import Markov.PaperSimpleGeneratorCalibration

noncomputable section
open Topology
namespace Markov

/-- The half-period is its own additive inverse, using the actual circle period. -/
theorem standardCircleHalf_neg : -standardCircleHalf = standardCircleHalf := by
  have hh : standardCircleHalf + standardCircleHalf = 0 := by
    change (((1/2+1/2 : ℝ)) : NormalizedCircle) = 0
    norm_num [AddCircle.coe_period]
  calc
    -standardCircleHalf = -standardCircleHalf + (standardCircleHalf + standardCircleHalf) := by rw [hh]; simp
    _ = standardCircleHalf := by abel

/-- The actual chart from the positive standard surgery model to the original
A/B convention is signed swap followed by the actual quotient homeomorphism. -/
def originalNielsenChart : StandardPuncturedTorus ≃ₜ ModularTraceQuotient :=
  standardSignedSwapPuncturedTorusHomeomorph.trans modularTraceQuotientPuncturedTorusHomeomorph.symm

theorem originalNielsenChart_standard (z : StandardPuncturedTorus) :
    (modularTraceQuotientPuncturedTorusHomeomorph (originalNielsenChart z)).val =
      (-z.val.2, -z.val.1) := by
  change (modularTraceQuotientPuncturedTorusHomeomorph
    (modularTraceQuotientPuncturedTorusHomeomorph.symm _)).val = _
  rw [Homeomorph.apply_symm_apply]
  rfl

/-- The actual signed-swap chart carries the surgery base to the calibrated original basepoint. -/
theorem originalNielsenChart_base : originalNielsenChart surgeryBasePoint = paperGeneratorCenterPoint := by
  apply modularTraceQuotientPuncturedTorusHomeomorph.injective
  apply Subtype.ext
  rw [originalNielsenChart_standard, paperGeneratorCenterPoint_standard]
  change (-standardCircleHalf, -standardCircleHalf) = (standardCircleHalf, standardCircleHalf)
  rw [standardCircleHalf_neg]

/-- The actual puncture-preserving shear expressed in the original modular surface. -/
def originalNielsenHomeomorph : ModularTraceQuotient ≃ₜ ModularTraceQuotient :=
  (originalNielsenChart.symm.trans surgeryColumnShear).trans originalNielsenChart

/-- Literal conjugacy of the actual surface homeomorphism with the actual column shear. -/
theorem originalNielsenHomeomorph_chart (z : StandardPuncturedTorus) :
    originalNielsenHomeomorph (originalNielsenChart z) = originalNielsenChart (surgeryColumnShear z) := by
  change originalNielsenChart (surgeryColumnShear (originalNielsenChart.symm (originalNielsenChart z))) = _
  rw [Homeomorph.symm_apply_apply]

theorem originalNielsenHomeomorph_base :
    originalNielsenHomeomorph paperGeneratorCenterPoint = originalNielsenChart shearSurgeryDiagonalBasePoint := by
  rw [← originalNielsenChart_base, originalNielsenHomeomorph_chart, surgeryColumnShear_base]

/-- The actual basepoint connector is the chart image of the checked shear connector. -/
def originalNielsenConnector : Path paperGeneratorCenterPoint (originalNielsenHomeomorph paperGeneratorCenterPoint) :=
  (shearSurgeryConnector.map originalNielsenChart.continuous).cast originalNielsenChart_base.symm
    originalNielsenHomeomorph_base

/-- The actual positive standard horizontal loop in the calibrated original basepoint. -/
def originalNielsenHorizontalLoop : Path paperGeneratorCenterPoint paperGeneratorCenterPoint :=
  (surgeryHorizontalLoop.map originalNielsenChart.continuous).cast
    originalNielsenChart_base.symm originalNielsenChart_base.symm

/-- The actual positive standard vertical loop in the same original basepoint. -/
def originalNielsenVerticalLoop : Path paperGeneratorCenterPoint paperGeneratorCenterPoint :=
  (surgeryVerticalLoop.map originalNielsenChart.continuous).cast
    originalNielsenChart_base.symm originalNielsenChart_base.symm

private theorem horizontal_lift (t : unitInterval) : surgeryHorizontalLift t = (1/2+(t : ℝ), 1/2) := by
  simp [surgeryHorizontalLift, Path.segment_apply, AffineMap.lineMap_apply_module,
    surgeryBaseLift, surgeryMiddleLift]
  constructor <;> ring

private theorem vertical_lift (t : unitInterval) : surgeryVerticalLift t = (3/2, 1/2+(t : ℝ)) := by
  simp [surgeryVerticalLift, Path.segment_apply, AffineMap.lineMap_apply_module,
    surgeryMiddleLift, surgeryEndLift]
  constructor <;> ring

private theorem three_half : ((3/2 : ℝ) : NormalizedCircle) = standardCircleHalf := by
  change ((3/2 : ℝ) : NormalizedCircle) = ((1/2 : ℝ) : NormalizedCircle)
  convert AddCircle.coe_add_period (p := (1 : ℝ)) (1/2 : ℝ) using 1
  norm_num

/-- The transported positive horizontal loop is literally the calibrated simple A loop. -/
theorem originalNielsenHorizontalLoop_eq_A : originalNielsenHorizontalLoop = paperSimpleALoop := by
  ext t
  apply modularTraceQuotientPuncturedTorusHomeomorph.injective
  apply Subtype.ext
  change (modularTraceQuotientPuncturedTorusHomeomorph
    (originalNielsenChart (surgeryHorizontalLoop t))).val = _
  rw [originalNielsenChart_standard, paperSimpleALoop_standard]
  change (-(surgeryPlaneProjection (surgeryHorizontalLift t)).2,
    -(surgeryPlaneProjection (surgeryHorizontalLift t)).1) = _
  rw [horizontal_lift]
  change (-standardCircleHalf, -(standardCircleHalf + ((t : ℝ) : NormalizedCircle))) = _
  rw [standardCircleHalf_neg]
  apply Prod.ext
  · rfl
  · rw [neg_add_rev, standardCircleHalf_neg, sub_eq_add_neg]
    exact add_comm _ _

/-- The transported positive vertical loop is literally the calibrated simple B loop. -/
theorem originalNielsenVerticalLoop_eq_B : originalNielsenVerticalLoop = paperSimpleBLoop := by
  ext t
  apply modularTraceQuotientPuncturedTorusHomeomorph.injective
  apply Subtype.ext
  change (modularTraceQuotientPuncturedTorusHomeomorph
    (originalNielsenChart (surgeryVerticalLoop t))).val = _
  rw [originalNielsenChart_standard, paperSimpleBLoop_standard]
  change (-(surgeryPlaneProjection (surgeryVerticalLift t)).2,
    -(surgeryPlaneProjection (surgeryVerticalLift t)).1) = _
  rw [vertical_lift]
  change (-(standardCircleHalf + ((t : ℝ) : NormalizedCircle)), -((3/2 : ℝ) : NormalizedCircle)) = _
  rw [three_half, standardCircleHalf_neg]
  apply Prod.ext
  · rw [neg_add_rev, standardCircleHalf_neg, sub_eq_add_neg]
    exact add_comm _ _
  · rfl

/-- The actual based-loop map with the literal transported connector retained. -/
def originalNielsenRawLoop (γ : Path paperGeneratorCenterPoint paperGeneratorCenterPoint) :
    Path paperGeneratorCenterPoint paperGeneratorCenterPoint :=
  (originalNielsenConnector.trans (γ.map originalNielsenHomeomorph.continuous)).trans
    originalNielsenConnector.symm

private def standardShearImage (γ : Path surgeryBasePoint surgeryBasePoint) : Path surgeryBasePoint surgeryBasePoint :=
  (shearSurgeryConnector.trans
    ((γ.map surgeryColumnShear.continuous).cast surgeryColumnShear_base.symm surgeryColumnShear_base.symm)).trans
    shearSurgeryConnector.symm

/-- Pointwise transport of the actual connector-based shear loop, with all basepoint casts. -/
theorem originalNielsenRawLoop_transport (γ : Path surgeryBasePoint surgeryBasePoint) :
    originalNielsenRawLoop
      ((γ.map originalNielsenChart.continuous).cast originalNielsenChart_base.symm originalNielsenChart_base.symm) =
    ((standardShearImage γ).map originalNielsenChart.continuous).cast
      originalNielsenChart_base.symm originalNielsenChart_base.symm := by
  ext t
  simp only [originalNielsenRawLoop, originalNielsenConnector, standardShearImage,
    Path.cast_coe, Path.map_coe, Function.comp_apply, Path.trans_apply, Path.symm_apply]
  split_ifs <;> first | rfl | exact originalNielsenHomeomorph_chart _

/-- Actual raw A image is genuinely path homotopic to A, by the checked shear homotopy. -/
theorem originalNielsenRawLoop_A_homotopic :
    (originalNielsenRawLoop paperSimpleALoop).Homotopic paperSimpleALoop := by
  have h := (surgeryShearHorizontalBasedLoop_homotopic.map
    ⟨originalNielsenChart, originalNielsenChart.continuous⟩).pathCast
      originalNielsenChart_base.symm originalNielsenChart_base.symm
  have he := originalNielsenRawLoop_transport surgeryHorizontalLoop
  change originalNielsenRawLoop originalNielsenHorizontalLoop = _ at he
  rw [originalNielsenHorizontalLoop_eq_A] at he
  change (((standardShearImage surgeryHorizontalLoop).map originalNielsenChart.continuous).cast
    originalNielsenChart_base.symm originalNielsenChart_base.symm).Homotopic originalNielsenHorizontalLoop at h
  rw [← he, originalNielsenHorizontalLoop_eq_A] at h
  exact h

/-- Actual raw B image is genuinely path homotopic to A-then-B in traversal order. -/
theorem originalNielsenRawLoop_B_homotopic :
    (originalNielsenRawLoop paperSimpleBLoop).Homotopic (paperSimpleALoop.trans paperSimpleBLoop) := by
  have h := (surgeryShearVerticalBasedLoop_homotopic.map
    ⟨originalNielsenChart, originalNielsenChart.continuous⟩).pathCast
      originalNielsenChart_base.symm originalNielsenChart_base.symm
  have he := originalNielsenRawLoop_transport surgeryVerticalLoop
  change originalNielsenRawLoop originalNielsenVerticalLoop = _ at he
  rw [originalNielsenVerticalLoop_eq_B] at he
  have hp : ((surgeryHorizontalLoop.trans surgeryVerticalLoop).map originalNielsenChart.continuous).cast
      originalNielsenChart_base.symm originalNielsenChart_base.symm =
        originalNielsenHorizontalLoop.trans originalNielsenVerticalLoop := by
    ext t
    simp only [Path.map_coe, Path.cast_coe, Function.comp_apply, Path.trans_apply]
    split_ifs <;> rfl
  change (((standardShearImage surgeryVerticalLoop).map originalNielsenChart.continuous).cast
    originalNielsenChart_base.symm originalNielsenChart_base.symm).Homotopic _ at h
  rw [← he, hp, originalNielsenHorizontalLoop_eq_A, originalNielsenVerticalLoop_eq_B] at h
  exact h

/-- Genuine original marked raw A image. -/
theorem originalNielsenRawLoop_A_marked :
    modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk (originalNielsenRawLoop paperSimpleALoop))) = paperTraceFreeGroupBasis 0 := by
  rw [Path.Homotopic.Quotient.eq.mpr originalNielsenRawLoop_A_homotopic, paperSimpleALoop_marked]

/-- The reversed library multiplication makes the raw marked B image B*A. -/
theorem originalNielsenRawLoop_B_marked :
    modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk (originalNielsenRawLoop paperSimpleBLoop))) =
        paperTraceFreeGroupBasis 1 * paperTraceFreeGroupBasis 0 := by
  rw [Path.Homotopic.Quotient.eq.mpr originalNielsenRawLoop_B_homotopic]
  change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
    (FundamentalGroup.fromPath (.mk paperSimpleBLoop) * FundamentalGroup.fromPath (.mk paperSimpleALoop)) = _
  rw [map_mul, paperSimpleBLoop_marked, paperSimpleALoop_marked]

/-- Prepending the reversed actual simple A loop corrects the Nielsen product order. -/
def originalNielsenConnectorCorrected :
    Path paperGeneratorCenterPoint (originalNielsenHomeomorph paperGeneratorCenterPoint) :=
  paperSimpleALoop.symm.trans originalNielsenConnector

/-- The actual based-loop map using that corrected actual connector. -/
def originalNielsenCorrectedLoop (γ : Path paperGeneratorCenterPoint paperGeneratorCenterPoint) :
    Path paperGeneratorCenterPoint paperGeneratorCenterPoint :=
  (originalNielsenConnectorCorrected.trans (γ.map originalNielsenHomeomorph.continuous)).trans
    originalNielsenConnectorCorrected.symm

/-- Actual connector change is literal conjugation by the genuine A loop
in the library fundamental group, before applying the original marking. -/
theorem originalNielsenCorrectedLoop_conjugate (γ : Path paperGeneratorCenterPoint paperGeneratorCenterPoint) :
    FundamentalGroup.fromPath (.mk (originalNielsenCorrectedLoop γ)) =
      FundamentalGroup.fromPath (.mk paperSimpleALoop) *
        FundamentalGroup.fromPath (.mk (originalNielsenRawLoop γ)) *
          (FundamentalGroup.fromPath (.mk paperSimpleALoop))⁻¹ := by
  change Path.Homotopic.Quotient.mk _ =
    (Path.Homotopic.Quotient.mk paperSimpleALoop.symm).trans
      ((Path.Homotopic.Quotient.mk (originalNielsenRawLoop γ)).trans
        (Path.Homotopic.Quotient.mk paperSimpleALoop))
  simp only [originalNielsenCorrectedLoop, originalNielsenConnectorCorrected, originalNielsenRawLoop,
    Path.trans_symm, Path.symm_symm, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.trans_assoc]

/-- Corrected actual marked A image is A. -/
theorem originalNielsenCorrectedLoop_A_marked :
    modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk (originalNielsenCorrectedLoop paperSimpleALoop))) = paperTraceFreeGroupBasis 0 := by
  rw [originalNielsenCorrectedLoop_conjugate, map_mul, map_mul, map_inv,
    paperSimpleALoop_marked, originalNielsenRawLoop_A_marked]
  group

/-- Corrected actual marked B image is A*B, exactly the Farey left-move convention. -/
theorem originalNielsenCorrectedLoop_B_marked :
    modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk (originalNielsenCorrectedLoop paperSimpleBLoop))) =
        paperTraceFreeGroupBasis 0 * paperTraceFreeGroupBasis 1 := by
  rw [originalNielsenCorrectedLoop_conjugate, map_mul, map_mul, map_inv,
    paperSimpleALoop_marked, originalNielsenRawLoop_B_marked]
  group

end Markov
