import Markov.StandardMediantSurgery

/-! Concrete based path surgery aligned with the actual linear shear.
All statements retain path traversal order; no group multiplication convention
or generic Farey induction is assumed. -/

noncomputable section
open Set Topology
namespace Markov

def shearSurgeryDiagonalStartLift : SurgeryLiftPlane := (1, 1/2)
def shearSurgeryDiagonalEndLift : SurgeryLiftPlane := (2, 3/2)
def shearSurgeryConnectorLift : Path surgeryBaseLift shearSurgeryDiagonalStartLift :=
  Path.segment _ _
def shearSurgeryDiagonalLift : Path shearSurgeryDiagonalStartLift shearSurgeryDiagonalEndLift :=
  Path.segment _ _
def shearSurgeryReturnLift : Path shearSurgeryDiagonalEndLift surgeryEndLift :=
  Path.segment _ _
def shearSurgeryTargetLift : Path surgeryBaseLift surgeryEndLift :=
  (shearSurgeryConnectorLift.trans shearSurgeryDiagonalLift).trans shearSurgeryReturnLift

private theorem product_formula (t : unitInterval) :
    surgeryProductLift t = if (t : ℝ) ≤ 1/2 then
      (1/2+2*(t : ℝ), 1/2) else (3/2, 2*(t : ℝ)-1/2) := by
  simp only [surgeryProductLift, Path.trans_apply]
  split_ifs <;> simp [surgeryHorizontalLift, surgeryVerticalLift,
    surgeryBaseLift, surgeryMiddleLift, surgeryEndLift, Path.segment_apply,
    AffineMap.lineMap_apply_module] <;> ring_nf <;> simp

private theorem target_formula (t : unitInterval) :
    shearSurgeryTargetLift t = if (t : ℝ) ≤ 1/2 then
      (if (t : ℝ) ≤ 1/4 then
        (1/2+2*(t : ℝ), 1/2) else (4*(t : ℝ), 4*(t : ℝ)-1/2))
      else (5/2-(t : ℝ), 3/2) := by
  simp only [shearSurgeryTargetLift, Path.trans_apply]
  split_ifs <;> simp_all [shearSurgeryConnectorLift, shearSurgeryDiagonalLift,
    shearSurgeryReturnLift, surgeryBaseLift, shearSurgeryDiagonalStartLift,
    shearSurgeryDiagonalEndLift, surgeryEndLift, Path.segment_apply,
    AffineMap.lineMap_apply_module] <;> (first | trivial | (constructor <;> linarith))

private def shearWindow (z : SurgeryLiftPlane) : Prop :=
  0 < z.1 ∧ 0 < z.2 ∧ z.2 < 2 ∧ 2*z.1-z.2 ≤ 5/2

private theorem product_window (t : unitInterval) : shearWindow (surgeryProductLift t) := by
  rw [product_formula]
  split_ifs
  all_goals
    dsimp [shearWindow]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [t.property.1, t.property.2]

private theorem target_window (t : unitInterval) : shearWindow (shearSurgeryTargetLift t) := by
  rw [target_formula]
  split_ifs
  all_goals
    dsimp [shearWindow]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [t.property.1, t.property.2]

private theorem product_gap (t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    (surgeryProductLift t).2 < (surgeryProductLift t).1 := by
  rw [product_formula]
  split_ifs <;> dsimp <;> linarith

private theorem target_gap (t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    (shearSurgeryTargetLift t).2 < (shearSurgeryTargetLift t).1 := by
  rw [target_formula]
  split_ifs <;> dsimp <;> linarith

/-- The explicit straight real homotopy to the shear-aligned target. -/
def shearSurgeryLiftHomotopy (s t : unitInterval) : SurgeryLiftPlane :=
  ((1-(s : ℝ))*(surgeryProductLift t).1 + (s : ℝ)*(shearSurgeryTargetLift t).1,
   (1-(s : ℝ))*(surgeryProductLift t).2 + (s : ℝ)*(shearSurgeryTargetLift t).2)

private theorem convex_pos {s x y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hx : 0 < x) (hy : 0 < y) : 0 < (1-s)*x+s*y := by
  by_cases hs : s = 0
  · simpa [hs] using hx
  · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have h1 := mul_pos hs' hy
    have h2 := mul_nonneg (sub_nonneg.mpr hs1) hx.le
    linarith

private theorem homotopy_window (s t : unitInterval) :
    shearWindow (shearSurgeryLiftHomotopy s t) := by
  have hL := product_window t
  have hM := target_window t
  dsimp [shearWindow] at hL hM ⊢
  dsimp [shearSurgeryLiftHomotopy]
  refine ⟨convex_pos s.property.1 s.property.2 hL.1 hM.1,
    convex_pos s.property.1 s.property.2 hL.2.1 hM.2.1, ?_, ?_⟩
  · have h := convex_pos s.property.1 s.property.2
      (sub_pos.mpr hL.2.2.1) (sub_pos.mpr hM.2.2.1)
    nlinarith
  · have h1 := mul_nonneg (sub_nonneg.mpr s.property.2)
      (sub_nonneg.mpr hL.2.2.2)
    have h2 := mul_nonneg s.property.1 (sub_nonneg.mpr hM.2.2.2)
    nlinarith

private theorem homotopy_gap (s t : unitInterval)
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    (shearSurgeryLiftHomotopy s t).2 < (shearSurgeryLiftHomotopy s t).1 := by
  have h := convex_pos s.property.1 s.property.2
    (sub_pos.mpr (product_gap t ht0 ht1)) (sub_pos.mpr (target_gap t ht0 ht1))
  dsimp [shearSurgeryLiftHomotopy]
  nlinarith

private theorem circle_zero_between {r : ℝ} (hr0 : 0 < r) (hr2 : r < 2)
    (hz : (r : AddCircle (1 : ℝ)) = 0) : r = 1 := by
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hz
  have hn' : (n : ℝ) = r := by simpa using hn
  have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hn2 : n < 2 := by exact_mod_cast (show (n : ℝ) < 2 by linarith)
  have hn1 : n = 1 := by omega
  simpa [hn1] using hn'.symm

private theorem projection_ne_zero_of_window {z : SurgeryLiftPlane}
    (hb : shearWindow z) (hgap : z.2 < z.1) : surgeryPlaneProjection z ≠ 0 := by
  intro hz
  have hy : z.2 = 1 := circle_zero_between hb.2.1 hb.2.2.1 (congrArg Prod.snd hz)
  have hx2 : z.1 < 2 := by linarith [hb.2.2.2]
  have hx : z.1 = 1 := circle_zero_between hb.1 hx2 (congrArg Prod.fst hz)
  linarith

private theorem half_period : ((3/2 : ℝ) : AddCircle (1 : ℝ)) =
    ((1/2 : ℝ) : AddCircle (1 : ℝ)) := by
  convert AddCircle.coe_add_period (p := (1 : ℝ)) (1/2 : ℝ) using 1
  norm_num

private theorem end_projection_eq_base : surgeryPlaneProjection surgeryEndLift =
    surgeryPlaneProjection surgeryBaseLift := by
  apply Prod.ext <;> exact half_period

private theorem homotopy_source (s : unitInterval) :
    shearSurgeryLiftHomotopy s 0 = surgeryBaseLift := by
  simp [shearSurgeryLiftHomotopy, surgeryBaseLift]
  ring

private theorem homotopy_target (s : unitInterval) :
    shearSurgeryLiftHomotopy s 1 = surgeryEndLift := by
  simp [shearSurgeryLiftHomotopy, surgeryEndLift]
  ring

private theorem homotopy_zero (t : unitInterval) :
    shearSurgeryLiftHomotopy 0 t = surgeryProductLift t := by
  ext <;> simp [shearSurgeryLiftHomotopy]

private theorem homotopy_one (t : unitInterval) :
    shearSurgeryLiftHomotopy 1 t = shearSurgeryTargetLift t := by
  ext <;> simp [shearSurgeryLiftHomotopy]

/-- Every point of the shear-aligned homotopy avoids every actual lattice puncture.
The linear bound 2x-y≤5/2 excludes (2,1), while interior x>y excludes (1,1). -/
theorem shearSurgeryLiftHomotopy_avoids_puncture (s t : unitInterval) :
    surgeryPlaneProjection (shearSurgeryLiftHomotopy s t) ≠ 0 := by
  by_cases h0 : t = 0
  · subst t
    rw [homotopy_source]
    exact surgeryBasePoint.property
  by_cases h1 : t = 1
  · subst t
    rw [homotopy_target, end_projection_eq_base]
    exact surgeryBasePoint.property
  exact projection_ne_zero_of_window (homotopy_window s t)
    (homotopy_gap s t (unitInterval.pos_iff_ne_zero.mpr h0)
      (unitInterval.lt_one_iff_ne_one.mpr h1))

private theorem projection_continuous : Continuous surgeryPlaneProjection :=
  ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd)

/-- The actual projected shear-aligned connector-diagonal-return loop. -/
def shearSurgeryTargetLoop : Path surgeryBasePoint surgeryBasePoint where
  toFun t := ⟨surgeryPlaneProjection (shearSurgeryTargetLift t), by
    simpa only [homotopy_one] using shearSurgeryLiftHomotopy_avoids_puncture 1 t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact projection_continuous.comp shearSurgeryTargetLift.continuous
  source' := by apply Subtype.ext; exact congrArg surgeryPlaneProjection shearSurgeryTargetLift.source
  target' := by
    apply Subtype.ext
    exact (congrArg surgeryPlaneProjection shearSurgeryTargetLift.target).trans end_projection_eq_base

/-- An actual endpoint-fixed homotopy to the shear-aligned target. -/
def shearSurgeryProductHomotopy : Path.Homotopy surgeryProductLoop shearSurgeryTargetLoop where
  toFun st := ⟨surgeryPlaneProjection (shearSurgeryLiftHomotopy st.1 st.2),
    shearSurgeryLiftHomotopy_avoids_puncture st.1 st.2⟩
  continuous_toFun := by
    unfold surgeryPlaneProjection shearSurgeryLiftHomotopy
    fun_prop
  map_zero_left t := by apply Subtype.ext; exact congrArg surgeryPlaneProjection (homotopy_zero t)
  map_one_left t := by apply Subtype.ext; exact congrArg surgeryPlaneProjection (homotopy_one t)
  prop' s t ht := by
    rcases ht with rfl | rfl
    · apply Subtype.ext
      change surgeryPlaneProjection (shearSurgeryLiftHomotopy s 0) =
        surgeryPlaneProjection (surgeryProductLift 0)
      rw [homotopy_source, surgeryProductLift.source]
    · apply Subtype.ext
      change surgeryPlaneProjection (shearSurgeryLiftHomotopy s 1) =
        surgeryPlaneProjection (surgeryProductLift 1)
      rw [homotopy_target, surgeryProductLift.target]

/-- Actual positive path traversal order: horizontal, then vertical. -/
theorem shearSurgeryHorizontal_trans_vertical_homotopic :
    (surgeryHorizontalLoop.trans surgeryVerticalLoop).Homotopic shearSurgeryTargetLoop := by
  rw [← surgeryProductLoop_eq_trans]
  exact ⟨shearSurgeryProductHomotopy⟩

/-- The final lifted segment is the initial connector reversed and translated by (1,1). -/
theorem shearSurgeryReturnLift_eq_translated_reverse (t : unitInterval) :
    shearSurgeryReturnLift t =
      ((shearSurgeryConnectorLift.symm t).1 + 1, (shearSurgeryConnectorLift.symm t).2 + 1) := by
  simp [shearSurgeryReturnLift, shearSurgeryConnectorLift, Path.segment_apply,
    AffineMap.lineMap_apply_module, shearSurgeryDiagonalEndLift, surgeryEndLift,
    surgeryBaseLift, shearSurgeryDiagonalStartLift]
  ring_nf
  simp

private theorem diagonal_formula (t : unitInterval) :
    shearSurgeryDiagonalLift t = (1+(t : ℝ), 1/2+(t : ℝ)) := by
  simp [shearSurgeryDiagonalLift, Path.segment_apply, AffineMap.lineMap_apply_module,
    shearSurgeryDiagonalStartLift, shearSurgeryDiagonalEndLift]
  constructor <;> ring

private theorem connector_avoids (t : unitInterval) :
    surgeryPlaneProjection (shearSurgeryConnectorLift t) ≠ 0 := by
  intro hz
  have hy := congrArg Prod.snd hz
  have he : (shearSurgeryConnectorLift t).2 = 1/2 := by
    simp [shearSurgeryConnectorLift, Path.segment_apply, AffineMap.lineMap_apply_module,
      surgeryBaseLift, shearSurgeryDiagonalStartLift]
    ring
  change (((shearSurgeryConnectorLift t).2 : ℝ) : AddCircle (1 : ℝ)) = 0 at hy
  rw [he] at hy
  exact standardCircleHalf_ne_zero hy

private theorem diagonal_avoids (t : unitInterval) :
    surgeryPlaneProjection (shearSurgeryDiagonalLift t) ≠ 0 := by
  apply projection_ne_zero_of_window
  · rw [diagonal_formula]
    dsimp [shearWindow]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [t.property.1, t.property.2]
  · rw [diagonal_formula]
    dsimp
    linarith

/-- The shear-aligned diagonal is exactly the existing embedded (1,1) affine
circle with (0,1) complement and half offset, with no circle-parameter shift. -/
theorem shearSurgeryDiagonalLift_projection_affine (t : unitInterval) :
    surgeryPlaneProjection (shearSurgeryDiagonalLift t) =
      (standardPuncturedAffineCircle (1,1) (0,1) (by norm_num [intDet])
        standardCircleHalf standardCircleHalf_ne_zero
          ((t : ℝ) : AddCircle (1 : ℝ))).val := by
  rw [diagonal_formula]
  apply Prod.ext
  · change (((1+(t : ℝ) : ℝ)) : AddCircle (1 : ℝ)) =
      (1 : ℤ) • ((t : ℝ) : AddCircle (1 : ℝ)) + (0 : ℤ) • standardCircleHalf
    simp only [one_zsmul, zero_zsmul, add_zero]
    rw [add_comm, AddCircle.coe_add_period]
  · change (((1/2+(t : ℝ) : ℝ)) : AddCircle (1 : ℝ)) =
      (1 : ℤ) • ((t : ℝ) : AddCircle (1 : ℝ)) + (1 : ℤ) • standardCircleHalf
    simp only [one_zsmul]
    change (((1/2+(t : ℝ) : ℝ)) : AddCircle (1 : ℝ)) =
      ((((t : ℝ)+1/2 : ℝ)) : AddCircle (1 : ℝ))
    rw [add_comm]

/-- The actual basepoint of the shear image of the vertical circle. -/
def shearSurgeryDiagonalBasePoint : StandardPuncturedTorus :=
  ⟨surgeryPlaneProjection shearSurgeryDiagonalStartLift, by
    simpa only [shearSurgeryDiagonalLift.source] using diagonal_avoids 0⟩

private theorem diagonal_end_projection : surgeryPlaneProjection shearSurgeryDiagonalEndLift =
    surgeryPlaneProjection shearSurgeryDiagonalStartLift := by
  apply Prod.ext
  · change ((2 : ℝ) : AddCircle (1 : ℝ)) = ((1 : ℝ) : AddCircle (1 : ℝ))
    convert AddCircle.coe_add_period (p := (1 : ℝ)) (1 : ℝ) using 1
    norm_num
  · exact half_period

/-- The horizontal actual connector from the original basepoint to the sheared basepoint. -/
def shearSurgeryConnector : Path surgeryBasePoint shearSurgeryDiagonalBasePoint where
  toFun t := ⟨surgeryPlaneProjection (shearSurgeryConnectorLift t), connector_avoids t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact projection_continuous.comp shearSurgeryConnectorLift.continuous
  source' := by apply Subtype.ext; exact congrArg surgeryPlaneProjection shearSurgeryConnectorLift.source
  target' := by apply Subtype.ext; exact congrArg surgeryPlaneProjection shearSurgeryConnectorLift.target

/-- The actual once-around embedded diagonal image of the vertical loop. -/
def shearSurgeryDiagonalLoop : Path shearSurgeryDiagonalBasePoint shearSurgeryDiagonalBasePoint where
  toFun t := ⟨surgeryPlaneProjection (shearSurgeryDiagonalLift t), diagonal_avoids t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact projection_continuous.comp shearSurgeryDiagonalLift.continuous
  source' := by apply Subtype.ext; exact congrArg surgeryPlaneProjection shearSurgeryDiagonalLift.source
  target' := by
    apply Subtype.ext
    exact (congrArg surgeryPlaneProjection shearSurgeryDiagonalLift.target).trans diagonal_end_projection

/-- The actual target retains exactly the horizontal connector, diagonal, and connector reversal. -/
theorem shearSurgeryTargetLoop_eq_connector_diagonal_reverse :
    shearSurgeryTargetLoop =
      (shearSurgeryConnector.trans shearSurgeryDiagonalLoop).trans shearSurgeryConnector.symm := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change surgeryPlaneProjection (shearSurgeryTargetLift t) = _
  simp only [shearSurgeryTargetLift, Path.trans_apply]
  split_ifs
  · rfl
  · rfl
  · change surgeryPlaneProjection (shearSurgeryReturnLift _) =
      surgeryPlaneProjection (shearSurgeryConnectorLift.symm _)
    rw [shearSurgeryReturnLift_eq_translated_reverse]
    apply Prod.ext
    · exact AddCircle.coe_add_period (p := (1 : ℝ)) _
    · exact AddCircle.coe_add_period (p := (1 : ℝ)) _

/-- Genuine shear-aligned surgery in positive PATH traversal order. Under the
library's reversed fundamental-group multiplication, this theorem alone is
not a claim that the corresponding group generator maps to U*V. -/
theorem shearSurgeryPositiveProduct_homotopic_embeddedDiagonal :
    (surgeryHorizontalLoop.trans surgeryVerticalLoop).Homotopic
      ((shearSurgeryConnector.trans shearSurgeryDiagonalLoop).trans shearSurgeryConnector.symm) := by
  rw [← shearSurgeryTargetLoop_eq_connector_diagonal_reverse]
  exact shearSurgeryHorizontal_trans_vertical_homotopic

end Markov
