import Markov.PaperSimpleGeneratorCalibration
import Markov.BasedHomeomorphFundamentalGroup

/-! Actual coordinate symmetries and their original nonabelian generator action.
The loop images are proved pointwise before passing through the actual based
fundamental-group equivalence and the original marking. -/

noncomputable section
open Topology
namespace Markov

private def restrictPunctured (f : StandardTorus ≃ₜ StandardTorus) (h0 : f 0 = 0) :
    StandardPuncturedTorus ≃ₜ StandardPuncturedTorus :=
  f.subtype (fun z => by
    constructor
    · intro hz he
      apply hz
      apply f.injective
      exact he.trans h0.symm
    · intro hz he
      apply hz
      rw [he, h0])

/-- The literal interchange of the two actual circle coordinates. -/
def standardCoordinateSwapTorusHomeomorph : StandardTorus ≃ₜ StandardTorus where
  toFun z := (z.2, z.1)
  invFun z := (z.2, z.1)
  left_inv _z := rfl
  right_inv _z := rfl
  continuous_toFun := continuous_snd.prodMk continuous_fst
  continuous_invFun := continuous_snd.prodMk continuous_fst

/-- The actual coordinate interchange restricts to the actual puncture complement. -/
def standardCoordinateSwapPuncturedTorusHomeomorph :
    StandardPuncturedTorus ≃ₜ StandardPuncturedTorus :=
  restrictPunctured standardCoordinateSwapTorusHomeomorph rfl

@[simp] theorem standardCoordinateSwapPuncturedTorusHomeomorph_coe
    (z : StandardPuncturedTorus) :
    (standardCoordinateSwapPuncturedTorusHomeomorph z).val = (z.val.2, z.val.1) := rfl

/-- Actual modular-surface coordinate interchange via the proved actual chart. -/
def modularCoordinateSwapHomeomorph : ModularTraceQuotient ≃ₜ ModularTraceQuotient :=
  (modularTraceQuotientPuncturedTorusHomeomorph.trans
    standardCoordinateSwapPuncturedTorusHomeomorph).trans
      modularTraceQuotientPuncturedTorusHomeomorph.symm

theorem modularCoordinateSwapHomeomorph_standard (z : ModularTraceQuotient) :
    modularTraceQuotientPuncturedTorusHomeomorph (modularCoordinateSwapHomeomorph z) =
      standardCoordinateSwapPuncturedTorusHomeomorph
        (modularTraceQuotientPuncturedTorusHomeomorph z) :=
  Homeomorph.apply_symm_apply _ _

/-- Coordinate interchange fixes the actual common original-generator basepoint. -/
theorem modularCoordinateSwapHomeomorph_center :
    modularCoordinateSwapHomeomorph paperGeneratorCenterPoint = paperGeneratorCenterPoint := by
  apply modularTraceQuotientPuncturedTorusHomeomorph.injective
  rw [modularCoordinateSwapHomeomorph_standard]
  apply Subtype.ext
  rw [standardCoordinateSwapPuncturedTorusHomeomorph_coe, paperGeneratorCenterPoint_standard]

/-- The actual simple A path maps pointwise to the actual calibrated B path. -/
theorem modularCoordinateSwapHomeomorph_A (t : unitInterval) :
    modularCoordinateSwapHomeomorph (paperSimpleALoop t) = paperSimpleBLoop t := by
  apply modularTraceQuotientPuncturedTorusHomeomorph.injective
  rw [modularCoordinateSwapHomeomorph_standard]
  apply Subtype.ext
  rw [standardCoordinateSwapPuncturedTorusHomeomorph_coe,
    paperSimpleALoop_standard, paperSimpleBLoop_standard]

/-- The actual simple B path maps pointwise to the actual calibrated A path. -/
theorem modularCoordinateSwapHomeomorph_B (t : unitInterval) :
    modularCoordinateSwapHomeomorph (paperSimpleBLoop t) = paperSimpleALoop t := by
  apply modularTraceQuotientPuncturedTorusHomeomorph.injective
  rw [modularCoordinateSwapHomeomorph_standard]
  apply Subtype.ext
  rw [standardCoordinateSwapPuncturedTorusHomeomorph_coe,
    paperSimpleBLoop_standard, paperSimpleALoop_standard]

private def fixedConnector {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    (x : X) (hx : f x = x) : Path x (f x) := (Path.refl x).cast rfl hx

private theorem fixedBasedEquiv_loop {X : Type*} [TopologicalSpace X]
    (f : X ≃ₜ X) (x : X) (hx : f x = x) (γ : Path x x) :
    basedHomeomorphFundamentalGroupEquiv f x (fixedConnector f x hx)
      (FundamentalGroup.fromPath (.mk γ)) =
        FundamentalGroup.fromPath (.mk ((γ.map f.continuous).cast hx.symm hx.symm)) := by
  rw [basedHomeomorphFundamentalGroupEquiv_loop]
  let δ := (γ.map f.continuous).cast hx.symm hx.symm
  have he : (((fixedConnector f x hx).trans (γ.map f.continuous)).trans
      (fixedConnector f x hx).symm) = ((Path.refl x).trans δ).trans (Path.refl x) := by
    apply Path.ext
    funext t
    simp only [Path.trans_apply]
    split_ifs <;> rfl
  rw [he]
  change ((Path.Homotopic.Quotient.refl x).trans (.mk δ)).trans
    (Path.Homotopic.Quotient.refl x) = .mk δ
  rw [Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_refl]

private theorem swap_mapped_A :
    (paperSimpleALoop.map modularCoordinateSwapHomeomorph.continuous).cast
      modularCoordinateSwapHomeomorph_center.symm modularCoordinateSwapHomeomorph_center.symm =
        paperSimpleBLoop := by
  apply Path.ext
  funext t
  exact modularCoordinateSwapHomeomorph_A t

private theorem swap_mapped_B :
    (paperSimpleBLoop.map modularCoordinateSwapHomeomorph.continuous).cast
      modularCoordinateSwapHomeomorph_center.symm modularCoordinateSwapHomeomorph_center.symm =
        paperSimpleALoop := by
  apply Path.ext
  funext t
  exact modularCoordinateSwapHomeomorph_B t

/-- The genuine based pi1 automorphism of actual coordinate interchange. -/
def modularCoordinateSwapFundamentalGroupEquiv :
    FundamentalGroup ModularTraceQuotient paperGeneratorCenterPoint ≃*
      FundamentalGroup ModularTraceQuotient paperGeneratorCenterPoint :=
  basedHomeomorphFundamentalGroupEquiv modularCoordinateSwapHomeomorph paperGeneratorCenterPoint
    (fixedConnector _ _ modularCoordinateSwapHomeomorph_center)

/-- Actual coordinate interchange expressed in the original nonabelian marking. -/
def originalCoordinateSwapMarkedEquiv : modularTraceSubgroup ≃* modularTraceSubgroup :=
  ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm.trans
    modularCoordinateSwapFundamentalGroupEquiv).trans
      (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift)

private theorem marked_symm_A :
    (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm (paperTraceFreeGroupBasis 0) =
      FundamentalGroup.fromPath (.mk paperSimpleALoop) := by
  apply (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).injective
  rw [MulEquiv.apply_symm_apply, paperSimpleALoop_marked]

private theorem marked_symm_B :
    (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm (paperTraceFreeGroupBasis 1) =
      FundamentalGroup.fromPath (.mk paperSimpleBLoop) := by
  apply (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).injective
  rw [MulEquiv.apply_symm_apply, paperSimpleBLoop_marked]

/-- Exact actual nonabelian generator image A↦B. -/
theorem originalCoordinateSwapMarkedEquiv_A :
    originalCoordinateSwapMarkedEquiv (paperTraceFreeGroupBasis 0) = paperTraceFreeGroupBasis 1 := by
  change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
    (modularCoordinateSwapFundamentalGroupEquiv
      ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm (paperTraceFreeGroupBasis 0))) = _
  rw [marked_symm_A]
  have he := fixedBasedEquiv_loop modularCoordinateSwapHomeomorph paperGeneratorCenterPoint
    modularCoordinateSwapHomeomorph_center paperSimpleALoop
  rw [swap_mapped_A] at he
  exact (congrArg (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift) he).trans
    paperSimpleBLoop_marked

/-- Exact actual nonabelian generator image B↦A. -/
theorem originalCoordinateSwapMarkedEquiv_B :
    originalCoordinateSwapMarkedEquiv (paperTraceFreeGroupBasis 1) = paperTraceFreeGroupBasis 0 := by
  change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
    (modularCoordinateSwapFundamentalGroupEquiv
      ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm (paperTraceFreeGroupBasis 1))) = _
  rw [marked_symm_B]
  have he := fixedBasedEquiv_loop modularCoordinateSwapHomeomorph paperGeneratorCenterPoint
    modularCoordinateSwapHomeomorph_center paperSimpleBLoop
  rw [swap_mapped_B] at he
  exact (congrArg (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift) he).trans
    paperSimpleALoop_marked

private theorem half_neg : -standardCircleHalf = standardCircleHalf := by
  have hh : standardCircleHalf + standardCircleHalf = 0 := by
    change (((1/2+1/2 : ℝ)) : NormalizedCircle) = 0
    norm_num [AddCircle.coe_period]
  calc
    -standardCircleHalf = -standardCircleHalf + (standardCircleHalf + standardCircleHalf) := by rw [hh]; simp
    _ = standardCircleHalf := by abel

/-- Literal reflection of the first actual circle coordinate. -/
def standardFirstReflectionTorusHomeomorph : StandardTorus ≃ₜ StandardTorus where
  toFun z := (-z.1, z.2)
  invFun z := (-z.1, z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The first-coordinate reflection restricts to the actual puncture complement. -/
def standardFirstReflectionPuncturedTorusHomeomorph :
    StandardPuncturedTorus ≃ₜ StandardPuncturedTorus :=
  restrictPunctured standardFirstReflectionTorusHomeomorph (by
    ext <;> simp [standardFirstReflectionTorusHomeomorph])

@[simp] theorem standardFirstReflectionPuncturedTorusHomeomorph_coe
    (z : StandardPuncturedTorus) :
    (standardFirstReflectionPuncturedTorusHomeomorph z).val = (-z.val.1, z.val.2) := rfl

/-- The actual modular-surface first-coordinate reflection. -/
def modularFirstReflectionHomeomorph : ModularTraceQuotient ≃ₜ ModularTraceQuotient :=
  (modularTraceQuotientPuncturedTorusHomeomorph.trans
    standardFirstReflectionPuncturedTorusHomeomorph).trans
      modularTraceQuotientPuncturedTorusHomeomorph.symm

theorem modularFirstReflectionHomeomorph_standard (z : ModularTraceQuotient) :
    modularTraceQuotientPuncturedTorusHomeomorph (modularFirstReflectionHomeomorph z) =
      standardFirstReflectionPuncturedTorusHomeomorph
        (modularTraceQuotientPuncturedTorusHomeomorph z) :=
  Homeomorph.apply_symm_apply _ _

/-- Reflection fixes the actual common original-generator basepoint modulo its period. -/
theorem modularFirstReflectionHomeomorph_center :
    modularFirstReflectionHomeomorph paperGeneratorCenterPoint = paperGeneratorCenterPoint := by
  apply modularTraceQuotientPuncturedTorusHomeomorph.injective
  rw [modularFirstReflectionHomeomorph_standard]
  apply Subtype.ext
  rw [standardFirstReflectionPuncturedTorusHomeomorph_coe, paperGeneratorCenterPoint_standard]
  apply Prod.ext
  · exact half_neg
  · rfl

/-- The actual vertical calibrated A loop is fixed pointwise by reflection. -/
theorem modularFirstReflectionHomeomorph_A (t : unitInterval) :
    modularFirstReflectionHomeomorph (paperSimpleALoop t) = paperSimpleALoop t := by
  apply modularTraceQuotientPuncturedTorusHomeomorph.injective
  rw [modularFirstReflectionHomeomorph_standard]
  apply Subtype.ext
  rw [standardFirstReflectionPuncturedTorusHomeomorph_coe, paperSimpleALoop_standard]
  apply Prod.ext
  · exact half_neg
  · rfl

/-- The horizontal calibrated B loop maps literally to its reversal. -/
theorem modularFirstReflectionHomeomorph_B (t : unitInterval) :
    modularFirstReflectionHomeomorph (paperSimpleBLoop t) = paperSimpleBLoop.symm t := by
  change modularFirstReflectionHomeomorph (paperSimpleBLoop t) =
    paperSimpleBLoop (unitInterval.symm t)
  apply modularTraceQuotientPuncturedTorusHomeomorph.injective
  rw [modularFirstReflectionHomeomorph_standard]
  apply Subtype.ext
  rw [standardFirstReflectionPuncturedTorusHomeomorph_coe,
    paperSimpleBLoop_standard, paperSimpleBLoop_standard]
  apply Prod.ext
  · change -(standardCircleHalf - ((t : ℝ) : NormalizedCircle)) =
      standardCircleHalf - (((1-(t : ℝ) : ℝ)) : NormalizedCircle)
    have ht : (((1-(t : ℝ) : ℝ)) : NormalizedCircle) = -((t : ℝ) : NormalizedCircle) := by
      change (((1 : ℝ) : NormalizedCircle) - ((t : ℝ) : NormalizedCircle)) = _
      rw [AddCircle.coe_period]
      exact zero_sub _
    calc
      -(standardCircleHalf - ((t : ℝ) : NormalizedCircle)) =
          ((t : ℝ) : NormalizedCircle) + standardCircleHalf := by
        rw [neg_sub, sub_eq_add_neg, half_neg]
      _ = standardCircleHalf - (((1-(t : ℝ) : ℝ)) : NormalizedCircle) := by
        rw [ht]
        abel
  · rfl

private theorem reflection_mapped_A :
    (paperSimpleALoop.map modularFirstReflectionHomeomorph.continuous).cast
      modularFirstReflectionHomeomorph_center.symm modularFirstReflectionHomeomorph_center.symm =
        paperSimpleALoop := by
  apply Path.ext
  funext t
  exact modularFirstReflectionHomeomorph_A t

private theorem reflection_mapped_B :
    (paperSimpleBLoop.map modularFirstReflectionHomeomorph.continuous).cast
      modularFirstReflectionHomeomorph_center.symm modularFirstReflectionHomeomorph_center.symm =
        paperSimpleBLoop.symm := by
  apply Path.ext
  funext t
  exact modularFirstReflectionHomeomorph_B t

/-- The genuine based pi1 automorphism induced by first-coordinate reflection. -/
def modularFirstReflectionFundamentalGroupEquiv :
    FundamentalGroup ModularTraceQuotient paperGeneratorCenterPoint ≃*
      FundamentalGroup ModularTraceQuotient paperGeneratorCenterPoint :=
  basedHomeomorphFundamentalGroupEquiv modularFirstReflectionHomeomorph paperGeneratorCenterPoint
    (fixedConnector _ _ modularFirstReflectionHomeomorph_center)

/-- Actual first-coordinate reflection in the original nonabelian marking. -/
def originalFirstReflectionMarkedEquiv : modularTraceSubgroup ≃* modularTraceSubgroup :=
  ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm.trans
    modularFirstReflectionFundamentalGroupEquiv).trans
      (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift)

/-- Exact nonabelian reflection image A↦A. -/
theorem originalFirstReflectionMarkedEquiv_A :
    originalFirstReflectionMarkedEquiv (paperTraceFreeGroupBasis 0) = paperTraceFreeGroupBasis 0 := by
  change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
    (modularFirstReflectionFundamentalGroupEquiv
      ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm (paperTraceFreeGroupBasis 0))) = _
  rw [marked_symm_A]
  have he := fixedBasedEquiv_loop modularFirstReflectionHomeomorph paperGeneratorCenterPoint
    modularFirstReflectionHomeomorph_center paperSimpleALoop
  rw [reflection_mapped_A] at he
  exact (congrArg (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift) he).trans
    paperSimpleALoop_marked

/-- Exact nonabelian reflection image B↦B⁻¹, proved through literal loop reversal. -/
theorem originalFirstReflectionMarkedEquiv_B :
    originalFirstReflectionMarkedEquiv (paperTraceFreeGroupBasis 1) = (paperTraceFreeGroupBasis 1)⁻¹ := by
  change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
    (modularFirstReflectionFundamentalGroupEquiv
      ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm (paperTraceFreeGroupBasis 1))) = _
  rw [marked_symm_B]
  have he := fixedBasedEquiv_loop modularFirstReflectionHomeomorph paperGeneratorCenterPoint
    modularFirstReflectionHomeomorph_center paperSimpleBLoop
  rw [reflection_mapped_B] at he
  have hm : modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk paperSimpleBLoop.symm)) = (paperTraceFreeGroupBasis 1)⁻¹ := by
    change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      ((FundamentalGroup.fromPath (.mk paperSimpleBLoop))⁻¹) = _
    rw [map_inv, paperSimpleBLoop_marked]
  exact (congrArg (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift) he).trans hm

end Markov
