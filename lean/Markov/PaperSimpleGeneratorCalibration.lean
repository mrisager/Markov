import Markov.ModularOriginalPrimitiveCircles

noncomputable section
open Topology
open scoped MatrixGroups
namespace Markov

/-- The literal center of the normalized punctured square. -/
def paperGeneratorSquareCenter : paperPuncturedSquare := ⟨(0, 0), by norm_num [paperPuncturedSquare]⟩

/-- The actual upper-half-plane lift used for the common original A/B basepoint. -/
def paperGeneratorCenterLift : UpperHalfPlane :=
  (paperMarkedQuadrilateralSquareHomeomorph.symm paperGeneratorSquareCenter).val

def paperGeneratorCenterPoint : ModularTraceQuotient := modularTraceQuotientMk paperGeneratorCenterLift

theorem paperGeneratorCenterPoint_standard :
    (modularTraceQuotientPuncturedTorusHomeomorph paperGeneratorCenterPoint).val =
      (standardCircleHalf, standardCircleHalf) := by
  change (modularTraceQuotientPuncturedTorusHomeomorph
    (modularTraceQuotientMk (paperMarkedQuadrilateralSquareHomeomorph.symm paperGeneratorSquareCenter).val)).val = _
  rw [modularTraceQuotientPuncturedTorusHomeomorph_mk, Homeomorph.apply_symm_apply,
    standardPuncturedTorusMap_coe]
  change (standardCircleSquareScalar 0, standardCircleSquareScalar 0) = _
  ext <;> norm_num [standardCircleSquareScalar, standardCircleHalf]

/-- The explicit center-to-top connector in the normalized square. -/
def paperGeneratorCenterToA : Path paperGeneratorSquareCenter paperSquareAStart where
  toFun t := ⟨(0, (t : ℝ)), by
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    have ht : |(t : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, ht1⟩
    refine ⟨by norm_num, ht, ?_⟩
    have hsq := paperSquare_coord_sq_le_one ht
    dsimp
    nlinarith⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; norm_num [paperGeneratorSquareCenter]
  target' := by apply Subtype.ext; norm_num [paperSquareAStart]

/-- The explicit center-to-right connector in the normalized square. -/
def paperGeneratorCenterToB : Path paperGeneratorSquareCenter paperSquareBStart where
  toFun t := ⟨((t : ℝ), 0), by
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    have ht : |(t : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, ht1⟩
    refine ⟨ht, by norm_num, ?_⟩
    have hsq := paperSquare_coord_sq_le_one ht
    dsimp
    nlinarith⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; norm_num [paperGeneratorSquareCenter]
  target' := by apply Subtype.ext; norm_num [paperSquareBStart]

def paperGeneratorCenterToALift : Path paperGeneratorCenterLift
    (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareAStart).val :=
  (paperGeneratorCenterToA.map paperMarkedQuadrilateralSquareHomeomorph.symm.continuous).map
    continuous_subtype_val

def paperGeneratorCenterToBLift : Path paperGeneratorCenterLift
    (paperMarkedQuadrilateralSquareHomeomorph.symm paperSquareBStart).val :=
  (paperGeneratorCenterToB.map paperMarkedQuadrilateralSquareHomeomorph.symm.continuous).map
    continuous_subtype_val

def paperGeneratorCenterAConnector := paperGeneratorCenterToALift.map modularTraceQuotientMk_continuous
def paperGeneratorCenterBConnector := paperGeneratorCenterToBLift.map modularTraceQuotientMk_continuous

/-- The explicit original A loop conjugated to the actual common center basepoint. -/
def paperGeneratorCenterALoop : Path paperGeneratorCenterPoint paperGeneratorCenterPoint :=
  (paperGeneratorCenterAConnector.trans paperSquareAOriginalLoop).trans paperGeneratorCenterAConnector.symm

/-- The explicit original B loop conjugated to the actual common center basepoint. -/
def paperGeneratorCenterBLoop : Path paperGeneratorCenterPoint paperGeneratorCenterPoint :=
  (paperGeneratorCenterBConnector.trans paperSquareBOriginalLoop).trans paperGeneratorCenterBConnector.symm

theorem modularTraceMarkedFundamentalGroupEquiv_projectedPath (z : UpperHalfPlane) (g : modularTraceSubgroup)
    (γ : Path z (g • z)) :
    modularTraceMarkedFundamentalGroupEquiv z (FundamentalGroup.fromPath (.mk
      ((γ.map modularTraceQuotientMk_continuous).cast rfl (modularTraceQuotientMk_smul g z).symm))) =
      modularTraceSeedConjugation g⁻¹ := by
  let δ := (γ.map modularTraceQuotientMk_continuous).cast rfl (modularTraceQuotientMk_smul g z).symm
  have he := coveringLoopEndpoint_projectedPath modularTraceQuotientMk_isCoveringMap
    γ (modularTraceQuotientMk_smul g z)
  have hd : modularTraceLoopDeckEquiv z (.mk δ) = g := by
    apply (modularTraceFibreEquiv z).injective
    rw [modularTraceLoopDeckEquiv_fibre]
    exact he
  change modularTraceSeedConjugation ((modularTraceLoopDeckEquiv z (.mk δ))⁻¹) = _
  rw [hd]

private def explicitForwardTransport (z w : UpperHalfPlane) (g : modularTraceSubgroup)
    (α : Path z w) (γ : Path w (g • w)) : Path z (g • z) :=
  (α.trans γ).trans (α.map (modularTraceSubgroup_isometry g).continuous).symm

private theorem explicitForwardTransport_projected (z w : UpperHalfPlane) (g : modularTraceSubgroup)
    (α : Path z w) (γ : Path w (g • w)) :
    (((explicitForwardTransport z w g α γ).map modularTraceQuotientMk_continuous).cast rfl
      (modularTraceQuotientMk_smul g z).symm) =
    ((α.map modularTraceQuotientMk_continuous).trans
      ((γ.map modularTraceQuotientMk_continuous).cast rfl (modularTraceQuotientMk_smul g w).symm)).trans
      (α.map modularTraceQuotientMk_continuous).symm := by
  ext t
  simp only [explicitForwardTransport, Path.cast_coe, Path.map_coe,
    Function.comp_apply, Path.trans_apply, Path.symm_apply]
  split_ifs <;> simp only [modularTraceQuotientMk_smul]

private theorem marked_conjugate_forward (z w : UpperHalfPlane) (g : modularTraceSubgroup)
    (α : Path z w) (γ : Path w (g • w)) :
    modularTraceMarkedFundamentalGroupEquiv z (FundamentalGroup.fromPath (.mk
      (((α.map modularTraceQuotientMk_continuous).trans
        ((γ.map modularTraceQuotientMk_continuous).cast rfl (modularTraceQuotientMk_smul g w).symm)).trans
        (α.map modularTraceQuotientMk_continuous).symm))) = modularTraceSeedConjugation g⁻¹ := by
  rw [← explicitForwardTransport_projected]
  exact modularTraceMarkedFundamentalGroupEquiv_projectedPath z g (explicitForwardTransport z w g α γ)

/-- Genuine original marked fundamental-group class of the actual center-based conjugate A loop. -/
theorem paperGeneratorCenterALoop_marked :
    modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk paperGeneratorCenterALoop)) = paperTraceFreeGroupBasis 0 := by
  have h := marked_conjugate_forward paperGeneratorCenterLift _ (paperTraceFreeGroupBasis 0)
    paperGeneratorCenterToALift paperSquareALiftedPath
  rw [modularTraceSeedConjugation_inv_basis] at h
  exact h

/-- Genuine original marked fundamental-group class of the actual center-based conjugate B loop. -/
theorem paperGeneratorCenterBLoop_marked :
    modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk paperGeneratorCenterBLoop)) = paperTraceFreeGroupBasis 1 := by
  have h := marked_conjugate_forward paperGeneratorCenterLift _ (paperTraceFreeGroupBasis 1)
    paperGeneratorCenterToBLift paperSquareBLiftedPath
  rw [modularTraceSeedConjugation_inv_basis] at h
  exact h

private theorem connectorA_first (t : unitInterval) :
    modularStandardFirstCoordinate (paperGeneratorCenterAConnector t) = standardCircleHalf := by
  change (modularTraceQuotientPuncturedTorusHomeomorph
    (modularTraceQuotientMk (paperMarkedQuadrilateralSquareHomeomorph.symm (paperGeneratorCenterToA t)).val)).val.1 = _
  rw [modularTraceQuotientPuncturedTorusHomeomorph_mk, Homeomorph.apply_symm_apply,
    standardPuncturedTorusMap_coe]
  change standardCircleSquareScalar 0 = standardCircleHalf
  norm_num [standardCircleSquareScalar, standardCircleHalf]

private theorem connectorB_second (t : unitInterval) :
    modularStandardSecondCoordinate (paperGeneratorCenterBConnector t) = standardCircleHalf := by
  change (modularTraceQuotientPuncturedTorusHomeomorph
    (modularTraceQuotientMk (paperMarkedQuadrilateralSquareHomeomorph.symm (paperGeneratorCenterToB t)).val)).val.2 = _
  rw [modularTraceQuotientPuncturedTorusHomeomorph_mk, Homeomorph.apply_symm_apply,
    standardPuncturedTorusMap_coe]
  change standardCircleSquareScalar 0 = standardCircleHalf
  norm_num [standardCircleSquareScalar, standardCircleHalf]

private theorem originalA_first (t : unitInterval) :
    modularStandardFirstCoordinate (paperSquareAOriginalLoop t) = standardCircleHalf := by
  unfold modularStandardFirstCoordinate
  rw [paperSquareAOriginalLoop_standard, standardPuncturedTorusMap_coe]
  change standardCircleSquareScalar 0 = standardCircleHalf
  norm_num [standardCircleSquareScalar, standardCircleHalf]

private theorem originalB_second (t : unitInterval) :
    modularStandardSecondCoordinate (paperSquareBOriginalLoop t) = standardCircleHalf := by
  unfold modularStandardSecondCoordinate
  rw [paperSquareBOriginalLoop_standard, standardPuncturedTorusMap_coe]
  change standardCircleSquareScalar 0 = standardCircleHalf
  norm_num [standardCircleSquareScalar, standardCircleHalf]

private theorem constantCoordinate_trans {X Y : Type} [TopologicalSpace X]
    {a b c : X} (f : X → Y) (k : Y) (α : Path a b) (β : Path b c)
    (hα : ∀ t, f (α t) = k) (hβ : ∀ t, f (β t) = k) (t : unitInterval) :
    f ((α.trans β) t) = k := by
  rw [Path.trans_apply]
  split_ifs
  · exact hα _
  · exact hβ _

/-- The actual conjugated A loop stays entirely on the vertical half-coordinate circle. -/
theorem paperGeneratorCenterALoop_first (t : unitInterval) :
    modularStandardFirstCoordinate (paperGeneratorCenterALoop t) = standardCircleHalf := by
  exact constantCoordinate_trans modularStandardFirstCoordinate standardCircleHalf
    (paperGeneratorCenterAConnector.trans paperSquareAOriginalLoop) paperGeneratorCenterAConnector.symm
    (constantCoordinate_trans modularStandardFirstCoordinate standardCircleHalf
      paperGeneratorCenterAConnector paperSquareAOriginalLoop connectorA_first originalA_first)
    (fun _ => connectorA_first _) t

/-- The actual conjugated B loop stays entirely on the horizontal half-coordinate circle. -/
theorem paperGeneratorCenterBLoop_second (t : unitInterval) :
    modularStandardSecondCoordinate (paperGeneratorCenterBLoop t) = standardCircleHalf := by
  exact constantCoordinate_trans modularStandardSecondCoordinate standardCircleHalf
    (paperGeneratorCenterBConnector.trans paperSquareBOriginalLoop) paperGeneratorCenterBConnector.symm
    (constantCoordinate_trans modularStandardSecondCoordinate standardCircleHalf
      paperGeneratorCenterBConnector paperSquareBOriginalLoop connectorB_second originalB_second)
    (fun _ => connectorB_second _) t

/-- The actual puncture-avoiding vertical circle through the common center. -/
def paperSimpleACircle (u : NormalizedCircle) : ModularTraceQuotient :=
  modularTraceQuotientPuncturedTorusHomeomorph.symm
    ⟨(standardCircleHalf, standardCircleHalf + u), by
      intro h
      exact standardCircleHalf_ne_zero (congrArg Prod.fst h)⟩

/-- The actual puncture-avoiding horizontal circle through the common center. -/
def paperSimpleBCircle (u : NormalizedCircle) : ModularTraceQuotient :=
  modularTraceQuotientPuncturedTorusHomeomorph.symm
    ⟨(standardCircleHalf + u, standardCircleHalf), by
      intro h
      exact standardCircleHalf_ne_zero (congrArg Prod.snd h)⟩

theorem continuous_paperSimpleACircle : Continuous paperSimpleACircle := by
  unfold paperSimpleACircle
  fun_prop

theorem continuous_paperSimpleBCircle : Continuous paperSimpleBCircle := by
  unfold paperSimpleBCircle
  fun_prop

theorem paperSimpleACircle_isClosedEmbedding : IsClosedEmbedding paperSimpleACircle := by
  apply continuous_paperSimpleACircle.isClosedEmbedding
  intro u v h
  have he := congrArg (fun z => (modularTraceQuotientPuncturedTorusHomeomorph z).val.2) h
  simp only [paperSimpleACircle, Homeomorph.apply_symm_apply] at he
  exact add_left_cancel he

theorem paperSimpleBCircle_isClosedEmbedding : IsClosedEmbedding paperSimpleBCircle := by
  apply continuous_paperSimpleBCircle.isClosedEmbedding
  intro u v h
  have he := congrArg (fun z => (modularTraceQuotientPuncturedTorusHomeomorph z).val.1) h
  simp only [paperSimpleBCircle, Homeomorph.apply_symm_apply] at he
  exact add_left_cancel he

theorem paperSimpleACircle_zero : paperSimpleACircle 0 = paperGeneratorCenterPoint := by
  apply modularTraceQuotientPuncturedTorusHomeomorph.injective
  change modularTraceQuotientPuncturedTorusHomeomorph
    (modularTraceQuotientPuncturedTorusHomeomorph.symm _) = _
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  rw [paperGeneratorCenterPoint_standard]
  simp

theorem paperSimpleBCircle_zero : paperSimpleBCircle 0 = paperGeneratorCenterPoint := by
  apply modularTraceQuotientPuncturedTorusHomeomorph.injective
  change modularTraceQuotientPuncturedTorusHomeomorph
    (modularTraceQuotientPuncturedTorusHomeomorph.symm _) = _
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  rw [paperGeneratorCenterPoint_standard]
  simp

/-- The literal negative vertical coordinate loop, based at the actual common center. -/
def paperSimpleALoop : Path paperGeneratorCenterPoint paperGeneratorCenterPoint :=
  ((normalizedCircleIntegerLoop (-1)).map continuous_paperSimpleACircle).cast
    paperSimpleACircle_zero.symm paperSimpleACircle_zero.symm

/-- The literal negative horizontal coordinate loop, based at the actual common center. -/
def paperSimpleBLoop : Path paperGeneratorCenterPoint paperGeneratorCenterPoint :=
  ((normalizedCircleIntegerLoop (-1)).map continuous_paperSimpleBCircle).cast
    paperSimpleBCircle_zero.symm paperSimpleBCircle_zero.symm

/-- Literal standard coordinates of the calibrated simple negative vertical loop. -/
theorem paperSimpleALoop_standard (t : unitInterval) :
    (modularTraceQuotientPuncturedTorusHomeomorph (paperSimpleALoop t)).val =
      (standardCircleHalf, standardCircleHalf - ((t : ℝ) : NormalizedCircle)) := by
  change (modularTraceQuotientPuncturedTorusHomeomorph
    (modularTraceQuotientPuncturedTorusHomeomorph.symm _)).val = _
  rw [Homeomorph.apply_symm_apply]
  simp only [normalizedCircleIntegerLoop_apply, Int.cast_neg, Int.cast_one,
    mul_neg, mul_one, AddCircle.coe_neg, sub_eq_add_neg]

/-- Literal standard coordinates of the calibrated simple negative horizontal loop. -/
theorem paperSimpleBLoop_standard (t : unitInterval) :
    (modularTraceQuotientPuncturedTorusHomeomorph (paperSimpleBLoop t)).val =
      (standardCircleHalf - ((t : ℝ) : NormalizedCircle), standardCircleHalf) := by
  change (modularTraceQuotientPuncturedTorusHomeomorph
    (modularTraceQuotientPuncturedTorusHomeomorph.symm _)).val = _
  rw [Homeomorph.apply_symm_apply]
  simp only [normalizedCircleIntegerLoop_apply, Int.cast_neg, Int.cast_one,
    mul_neg, mul_one, AddCircle.coe_neg, sub_eq_add_neg]

private theorem loop_homotopic_via_circle {X : Type} [TopologicalSpace X]
    {x : X} (f : NormalizedCircle → X) (hf : Continuous f) (hfx : f 0 = x)
    (r : X → NormalizedCircle) (hr : Continuous r) (hrx : r x = 0)
    (γ : Path x x) (hrecover : ∀ t, f (r (γ t)) = γ t) (n : ℤ)
    (hw : normalizedCircleWinding ((γ.map hr).cast hrx.symm hrx.symm) = n) :
    γ.Homotopic (((normalizedCircleIntegerLoop n).map hf).cast hfx.symm hfx.symm) := by
  let δ := (γ.map hr).cast hrx.symm hrx.symm
  have hh : δ.Homotopic (normalizedCircleIntegerLoop n) := by
    apply (normalizedCircleWinding_homotopic_iff _ _).mp
    exact hw.trans (normalizedCircleWinding_integerLoop n).symm
  have hm := (hh.map ⟨f, hf⟩).pathCast hfx.symm hfx.symm
  have he : ((δ.map hf).cast hfx.symm hfx.symm) = γ := by
    ext t
    exact hrecover t
  rw [he] at hm
  exact hm

/-- Genuine relative path homotopy from the original center-based A conjugate
to the literal simple vertical coordinate loop, entirely through the circle slice. -/
theorem paperGeneratorCenterALoop_homotopic_simple : paperGeneratorCenterALoop.Homotopic paperSimpleALoop := by
  let r := fun z => modularStandardSecondCoordinate z - modularStandardSecondCoordinate paperGeneratorCenterPoint
  have hr : Continuous r := continuous_modularStandardSecondCoordinate.sub continuous_const
  have hrx : r paperGeneratorCenterPoint = 0 := sub_self _
  apply loop_homotopic_via_circle paperSimpleACircle continuous_paperSimpleACircle
    paperSimpleACircle_zero r hr hrx paperGeneratorCenterALoop
  · intro t
    apply modularTraceQuotientPuncturedTorusHomeomorph.injective
    change modularTraceQuotientPuncturedTorusHomeomorph
      (modularTraceQuotientPuncturedTorusHomeomorph.symm _) = _
    rw [Homeomorph.apply_symm_apply]
    apply Subtype.ext
    apply Prod.ext
    · exact (paperGeneratorCenterALoop_first t).symm
    · change standardCircleHalf + r (paperGeneratorCenterALoop t) =
        modularStandardSecondCoordinate (paperGeneratorCenterALoop t)
      dsimp [r]
      have hz := congrArg Prod.snd paperGeneratorCenterPoint_standard
      change modularStandardSecondCoordinate paperGeneratorCenterPoint = standardCircleHalf at hz
      rw [hz]
      abel
  · change (modularStandardLoopWinding paperGeneratorCenterALoop).2 = -1
    have h := modularStandardH1Winding_loop paperGeneratorCenterALoop
    change modularStandardH1Winding (singularLoopClass ModularTraceQuotient
      ((paperGeneratorCenterAConnector.trans paperSquareAOriginalLoop).trans paperGeneratorCenterAConnector.symm)) = _ at h
    rw [singularLoopClass_conjugate, modularStandardH1Winding_generatorA] at h
    exact (congrArg Prod.snd h).symm

/-- Genuine relative path homotopy from the original center-based B conjugate
to the literal simple horizontal coordinate loop, entirely through the circle slice. -/
theorem paperGeneratorCenterBLoop_homotopic_simple : paperGeneratorCenterBLoop.Homotopic paperSimpleBLoop := by
  let r := fun z => modularStandardFirstCoordinate z - modularStandardFirstCoordinate paperGeneratorCenterPoint
  have hr : Continuous r := continuous_modularStandardFirstCoordinate.sub continuous_const
  have hrx : r paperGeneratorCenterPoint = 0 := sub_self _
  apply loop_homotopic_via_circle paperSimpleBCircle continuous_paperSimpleBCircle
    paperSimpleBCircle_zero r hr hrx paperGeneratorCenterBLoop
  · intro t
    apply modularTraceQuotientPuncturedTorusHomeomorph.injective
    change modularTraceQuotientPuncturedTorusHomeomorph
      (modularTraceQuotientPuncturedTorusHomeomorph.symm _) = _
    rw [Homeomorph.apply_symm_apply]
    apply Subtype.ext
    apply Prod.ext
    · change standardCircleHalf + r (paperGeneratorCenterBLoop t) =
        modularStandardFirstCoordinate (paperGeneratorCenterBLoop t)
      dsimp [r]
      have hz := congrArg Prod.fst paperGeneratorCenterPoint_standard
      change modularStandardFirstCoordinate paperGeneratorCenterPoint = standardCircleHalf at hz
      rw [hz]
      abel
    · exact (paperGeneratorCenterBLoop_second t).symm
  · change (modularStandardLoopWinding paperGeneratorCenterBLoop).1 = -1
    have h := modularStandardH1Winding_loop paperGeneratorCenterBLoop
    change modularStandardH1Winding (singularLoopClass ModularTraceQuotient
      ((paperGeneratorCenterBConnector.trans paperSquareBOriginalLoop).trans paperGeneratorCenterBConnector.symm)) = _ at h
    rw [singularLoopClass_conjugate, modularStandardH1Winding_generatorB] at h
    exact (congrArg Prod.fst h).symm

/-- The genuine original marked pi1 class of the simple vertical coordinate loop is literal A. -/
theorem paperSimpleALoop_marked :
    modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk paperSimpleALoop)) = paperTraceFreeGroupBasis 0 := by
  rw [← Path.Homotopic.Quotient.eq.mpr paperGeneratorCenterALoop_homotopic_simple]
  exact paperGeneratorCenterALoop_marked

/-- The genuine original marked pi1 class of the simple horizontal coordinate loop is literal B. -/
theorem paperSimpleBLoop_marked :
    modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk paperSimpleBLoop)) = paperTraceFreeGroupBasis 1 := by
  rw [← Path.Homotopic.Quotient.eq.mpr paperGeneratorCenterBLoop_homotopic_simple]
  exact paperGeneratorCenterBLoop_marked

end Markov
