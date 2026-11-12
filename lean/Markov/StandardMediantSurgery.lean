import Markov.StandardPrimitiveCircles
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Homotopy.Path

noncomputable section
open Set Topology
namespace Markov

abbrev SurgeryLiftPlane := ℝ × ℝ

def surgeryBaseLift : SurgeryLiftPlane := (1/2, 1/2)
def surgeryMiddleLift : SurgeryLiftPlane := (3/2, 1/2)
def surgeryEndLift : SurgeryLiftPlane := (3/2, 3/2)
def surgeryDiagonalStartLift : SurgeryLiftPlane := (3/4, 1/4)
def surgeryDiagonalEndLift : SurgeryLiftPlane := (7/4, 5/4)

def surgeryHorizontalLift : Path surgeryBaseLift surgeryMiddleLift :=
  Path.segment _ _
def surgeryVerticalLift : Path surgeryMiddleLift surgeryEndLift :=
  Path.segment _ _
def surgeryProductLift : Path surgeryBaseLift surgeryEndLift :=
  surgeryHorizontalLift.trans surgeryVerticalLift

def surgeryConnectorLift : Path surgeryBaseLift surgeryDiagonalStartLift :=
  Path.segment _ _
def surgeryDiagonalLift : Path surgeryDiagonalStartLift surgeryDiagonalEndLift :=
  Path.segment _ _
def surgeryReturnLift : Path surgeryDiagonalEndLift surgeryEndLift :=
  Path.segment _ _
def surgerySmoothedLift : Path surgeryBaseLift surgeryEndLift :=
  (surgeryConnectorLift.trans surgeryDiagonalLift).trans surgeryReturnLift

private theorem product_formula (t : unitInterval) :
    surgeryProductLift t = if (t : ℝ) ≤ 1/2 then
      (1/2+2*(t : ℝ), 1/2) else (3/2, 2*(t : ℝ)-1/2) := by
  simp only [surgeryProductLift, Path.trans_apply]
  split_ifs <;> simp [surgeryHorizontalLift, surgeryVerticalLift,
    surgeryBaseLift, surgeryMiddleLift, surgeryEndLift, Path.segment_apply,
    AffineMap.lineMap_apply_module] <;> ring_nf <;> simp

private theorem smooth_formula (t : unitInterval) :
    surgerySmoothedLift t = if (t : ℝ) ≤ 1/2 then
      (if (t : ℝ) ≤ 1/4 then
        (1/2+(t : ℝ), 1/2-(t : ℝ)) else (4*(t : ℝ)-1/4, 4*(t : ℝ)-3/4))
      else (2-(t : ℝ)/2, 1+(t : ℝ)/2) := by
  simp only [surgerySmoothedLift, Path.trans_apply]
  split_ifs <;> simp_all [surgeryConnectorLift, surgeryDiagonalLift, surgeryReturnLift,
    surgeryBaseLift, surgeryDiagonalStartLift, surgeryDiagonalEndLift, surgeryEndLift,
    Path.segment_apply, AffineMap.lineMap_apply_module] <;>
      (first | trivial | (constructor <;> linarith))

private def liftBox (z : SurgeryLiftPlane) : Prop :=
  0 < z.1 ∧ z.1 < 2 ∧ 0 < z.2 ∧ z.2 < 2

private theorem product_box (t : unitInterval) : liftBox (surgeryProductLift t) := by
  rw [product_formula]
  split_ifs
  all_goals
    dsimp [liftBox]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [t.property.1, t.property.2]

private theorem smooth_box (t : unitInterval) : liftBox (surgerySmoothedLift t) := by
  rw [smooth_formula]
  split_ifs
  all_goals
    dsimp [liftBox]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [t.property.1, t.property.2]

private theorem product_gap (t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    (surgeryProductLift t).2 < (surgeryProductLift t).1 := by
  rw [product_formula]
  split_ifs <;> dsimp <;> linarith

private theorem smooth_gap (t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    (surgerySmoothedLift t).2 < (surgerySmoothedLift t).1 := by
  rw [smooth_formula]
  split_ifs <;> dsimp <;> linarith

/-- The explicit straight interpolation of the two real PL lifts. -/
def surgeryLiftHomotopy (s t : unitInterval) : SurgeryLiftPlane :=
  ((1-(s : ℝ))*(surgeryProductLift t).1 + (s : ℝ)*(surgerySmoothedLift t).1,
   (1-(s : ℝ))*(surgeryProductLift t).2 + (s : ℝ)*(surgerySmoothedLift t).2)

private theorem convex_pos {s x y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hx : 0 < x) (hy : 0 < y) : 0 < (1-s)*x+s*y := by
  by_cases hs : s = 0
  · simpa [hs] using hx
  · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have h1 := mul_pos hs' hy
    have h2 := mul_nonneg (sub_nonneg.mpr hs1) hx.le
    linarith

private theorem homotopy_box (s t : unitInterval) : liftBox (surgeryLiftHomotopy s t) := by
  have hL := product_box t
  have hM := smooth_box t
  dsimp [liftBox] at hL hM ⊢
  dsimp [surgeryLiftHomotopy]
  refine ⟨convex_pos s.property.1 s.property.2 hL.1 hM.1, ?_,
    convex_pos s.property.1 s.property.2 hL.2.2.1 hM.2.2.1, ?_⟩
  · have h := convex_pos s.property.1 s.property.2
      (sub_pos.mpr hL.2.1) (sub_pos.mpr hM.2.1)
    nlinarith
  · have h := convex_pos s.property.1 s.property.2
      (sub_pos.mpr hL.2.2.2) (sub_pos.mpr hM.2.2.2)
    nlinarith

private theorem homotopy_gap (s t : unitInterval)
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    (surgeryLiftHomotopy s t).2 < (surgeryLiftHomotopy s t).1 := by
  have h := convex_pos s.property.1 s.property.2
    (sub_pos.mpr (product_gap t ht0 ht1)) (sub_pos.mpr (smooth_gap t ht0 ht1))
  dsimp [surgeryLiftHomotopy]
  nlinarith

/-- The literal real-plane projection to the actual two-circle torus. -/
def surgeryPlaneProjection (z : SurgeryLiftPlane) : StandardTorus :=
  ((z.1 : AddCircle (1 : ℝ)), (z.2 : AddCircle (1 : ℝ)))

private theorem projection_continuous : Continuous surgeryPlaneProjection :=
  ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd)

private theorem circle_zero_between {r : ℝ} (hr0 : 0 < r) (hr2 : r < 2)
    (hz : (r : AddCircle (1 : ℝ)) = 0) : r = 1 := by
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hz
  have hn' : (n : ℝ) = r := by simpa using hn
  have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hn2 : n < 2 := by exact_mod_cast (show (n : ℝ) < 2 by linarith)
  have hn1 : n = 1 := by omega
  simpa [hn1] using hn'.symm

private theorem projection_ne_zero_of_gap {z : SurgeryLiftPlane}
    (hb : liftBox z) (hgap : z.2 < z.1) : surgeryPlaneProjection z ≠ 0 := by
  intro hz
  have hx : z.1 = 1 := circle_zero_between hb.1 hb.2.1 (congrArg Prod.fst hz)
  have hy : z.2 = 1 := circle_zero_between hb.2.2.1 hb.2.2.2 (congrArg Prod.snd hz)
  linarith

private theorem half_period : ((3/2 : ℝ) : AddCircle (1 : ℝ)) =
    ((1/2 : ℝ) : AddCircle (1 : ℝ)) := by
  convert AddCircle.coe_add_period (p := (1 : ℝ)) (1/2 : ℝ) using 1
  norm_num

private theorem base_projection_ne_zero : surgeryPlaneProjection surgeryBaseLift ≠ 0 := by
  intro hz
  exact standardCircleHalf_ne_zero (congrArg Prod.fst hz)

private theorem end_projection_eq_base : surgeryPlaneProjection surgeryEndLift =
    surgeryPlaneProjection surgeryBaseLift := by
  apply Prod.ext <;> exact half_period

private theorem homotopy_source (s : unitInterval) :
    surgeryLiftHomotopy s 0 = surgeryBaseLift := by
  simp [surgeryLiftHomotopy, surgeryBaseLift]
  ring

private theorem homotopy_target (s : unitInterval) :
    surgeryLiftHomotopy s 1 = surgeryEndLift := by
  simp [surgeryLiftHomotopy, surgeryEndLift]
  ring

/-- Every point of the entire explicit straight homotopy avoids the actual puncture. -/
theorem surgeryLiftHomotopy_avoids_puncture (s t : unitInterval) :
    surgeryPlaneProjection (surgeryLiftHomotopy s t) ≠ 0 := by
  by_cases h0 : t = 0
  · subst t
    rw [homotopy_source]
    exact base_projection_ne_zero
  by_cases h1 : t = 1
  · subst t
    rw [homotopy_target, end_projection_eq_base]
    exact base_projection_ne_zero
  exact projection_ne_zero_of_gap (homotopy_box s t)
    (homotopy_gap s t (unitInterval.pos_iff_ne_zero.mpr h0)
      (unitInterval.lt_one_iff_ne_one.mpr h1))

private theorem homotopy_zero (t : unitInterval) :
    surgeryLiftHomotopy 0 t = surgeryProductLift t := by
  ext <;> simp [surgeryLiftHomotopy]

private theorem homotopy_one (t : unitInterval) :
    surgeryLiftHomotopy 1 t = surgerySmoothedLift t := by
  ext <;> simp [surgeryLiftHomotopy]

/-- The actual common basepoint, the class of (1/2,1/2). -/
def surgeryBasePoint : StandardPuncturedTorus :=
  ⟨surgeryPlaneProjection surgeryBaseLift, base_projection_ne_zero⟩

/-- The actual horizontal circle loop at the common basepoint. -/
def surgeryHorizontalLoop : Path surgeryBasePoint surgeryBasePoint where
  toFun t := ⟨surgeryPlaneProjection (surgeryHorizontalLift t), by
    intro hz
    have hy := congrArg Prod.snd hz
    have he : (surgeryHorizontalLift t).2 = 1/2 := by
      simp [surgeryHorizontalLift, Path.segment_apply,
        AffineMap.lineMap_apply_module, surgeryBaseLift, surgeryMiddleLift]
      ring
    change (((surgeryHorizontalLift t).2 : ℝ) : AddCircle (1 : ℝ)) = 0 at hy
    rw [he] at hy
    exact standardCircleHalf_ne_zero hy⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact projection_continuous.comp surgeryHorizontalLift.continuous
  source' := by
    apply Subtype.ext
    exact congrArg surgeryPlaneProjection surgeryHorizontalLift.source
  target' := by
    apply Subtype.ext
    change surgeryPlaneProjection (surgeryHorizontalLift 1) = _
    rw [surgeryHorizontalLift.target]
    apply Prod.ext
    · exact half_period
    · rfl

/-- The actual vertical circle loop, traversed after the horizontal loop. -/
def surgeryVerticalLoop : Path surgeryBasePoint surgeryBasePoint where
  toFun t := ⟨surgeryPlaneProjection (surgeryVerticalLift t), by
    intro hz
    have hx := congrArg Prod.fst hz
    have he : (surgeryVerticalLift t).1 = 3/2 := by
      simp [surgeryVerticalLift, Path.segment_apply,
        AffineMap.lineMap_apply_module, surgeryMiddleLift, surgeryEndLift]
      ring
    change (((surgeryVerticalLift t).1 : ℝ) : AddCircle (1 : ℝ)) = 0 at hx
    rw [he, half_period] at hx
    exact standardCircleHalf_ne_zero hx⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact projection_continuous.comp surgeryVerticalLift.continuous
  source' := by
    apply Subtype.ext
    change surgeryPlaneProjection (surgeryVerticalLift 0) = _
    rw [surgeryVerticalLift.source]
    apply Prod.ext
    · exact half_period
    · rfl
  target' := by
    apply Subtype.ext
    change surgeryPlaneProjection (surgeryVerticalLift 1) = _
    rw [surgeryVerticalLift.target]
    exact end_projection_eq_base

/-- Projection of the actual horizontal-then-vertical lifted product. -/
def surgeryProductLoop : Path surgeryBasePoint surgeryBasePoint where
  toFun t := ⟨surgeryPlaneProjection (surgeryProductLift t), by
    simpa only [homotopy_zero] using surgeryLiftHomotopy_avoids_puncture 0 t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact projection_continuous.comp surgeryProductLift.continuous
  source' := by apply Subtype.ext; exact congrArg surgeryPlaneProjection surgeryProductLift.source
  target' := by
    apply Subtype.ext
    exact (congrArg surgeryPlaneProjection surgeryProductLift.target).trans end_projection_eq_base

/-- The source is literally the positive horizontal loop followed by the positive vertical loop. -/
theorem surgeryProductLoop_eq_trans :
    surgeryProductLoop = surgeryHorizontalLoop.trans surgeryVerticalLoop := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change surgeryPlaneProjection (surgeryProductLift t) = _
  simp only [surgeryProductLift, Path.trans_apply]
  split_ifs <;> rfl

/-- The projected connector, diagonal, and translated reversed connector,
with the PL factorization retained in the lifted-path definition. -/
def surgerySmoothedLoop : Path surgeryBasePoint surgeryBasePoint where
  toFun t := ⟨surgeryPlaneProjection (surgerySmoothedLift t), by
    simpa only [homotopy_one] using surgeryLiftHomotopy_avoids_puncture 1 t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact projection_continuous.comp surgerySmoothedLift.continuous
  source' := by apply Subtype.ext; exact congrArg surgeryPlaneProjection surgerySmoothedLift.source
  target' := by
    apply Subtype.ext
    exact (congrArg surgeryPlaneProjection surgerySmoothedLift.target).trans end_projection_eq_base

/-- A genuine endpoint-fixed path homotopy in the actual punctured torus,
obtained by the explicit lattice-avoiding real straight interpolation. -/
def surgeryProductHomotopy : Path.Homotopy surgeryProductLoop surgerySmoothedLoop where
  toFun st := ⟨surgeryPlaneProjection (surgeryLiftHomotopy st.1 st.2),
    surgeryLiftHomotopy_avoids_puncture st.1 st.2⟩
  continuous_toFun := by
    unfold surgeryPlaneProjection surgeryLiftHomotopy
    fun_prop
  map_zero_left t := by apply Subtype.ext; exact congrArg surgeryPlaneProjection (homotopy_zero t)
  map_one_left t := by apply Subtype.ext; exact congrArg surgeryPlaneProjection (homotopy_one t)
  prop' s t ht := by
    rcases ht with rfl | rfl
    · apply Subtype.ext
      change surgeryPlaneProjection (surgeryLiftHomotopy s 0) =
        surgeryPlaneProjection (surgeryProductLift 0)
      rw [homotopy_source, surgeryProductLift.source]
    · apply Subtype.ext
      change surgeryPlaneProjection (surgeryLiftHomotopy s 1) =
        surgeryPlaneProjection (surgeryProductLift 1)
      rw [homotopy_target, surgeryProductLift.target]

/-- The actual positive product has the proved concrete diagonal-with-connector representative. -/
theorem surgeryHorizontal_trans_vertical_homotopic :
    (surgeryHorizontalLoop.trans surgeryVerticalLoop).Homotopic surgerySmoothedLoop := by
  rw [← surgeryProductLoop_eq_trans]
  exact ⟨surgeryProductHomotopy⟩

/-- The final lifted segment is exactly the reversed initial connector translated by (1,1). -/
theorem surgeryReturnLift_eq_translated_reverse (t : unitInterval) :
    surgeryReturnLift t =
      ((surgeryConnectorLift.symm t).1 + 1, (surgeryConnectorLift.symm t).2 + 1) := by
  simp [surgeryReturnLift, surgeryConnectorLift, Path.segment_apply,
    AffineMap.lineMap_apply_module, surgeryDiagonalEndLift, surgeryEndLift,
    surgeryBaseLift, surgeryDiagonalStartLift]
  constructor <;> ring

private theorem connector_formula (t : unitInterval) :
    surgeryConnectorLift t = (1/2+(t : ℝ)/4, 1/2-(t : ℝ)/4) := by
  simp [surgeryConnectorLift, Path.segment_apply, AffineMap.lineMap_apply_module,
    surgeryBaseLift, surgeryDiagonalStartLift]
  constructor <;> ring

private theorem diagonal_formula (t : unitInterval) :
    surgeryDiagonalLift t = (3/4+(t : ℝ), 1/4+(t : ℝ)) := by
  simp [surgeryDiagonalLift, Path.segment_apply, AffineMap.lineMap_apply_module,
    surgeryDiagonalStartLift, surgeryDiagonalEndLift]
  constructor <;> ring

private theorem connector_avoids (t : unitInterval) :
    surgeryPlaneProjection (surgeryConnectorLift t) ≠ 0 := by
  rw [connector_formula]
  intro hz
  have hx : (1/2+(t : ℝ)/4 : ℝ) = 1 := circle_zero_between
    (by linarith [t.property.1]) (by linarith [t.property.2]) (congrArg Prod.fst hz)
  linarith [t.property.2]

private theorem diagonal_avoids (t : unitInterval) :
    surgeryPlaneProjection (surgeryDiagonalLift t) ≠ 0 := by
  apply projection_ne_zero_of_gap
  · rw [diagonal_formula]
    dsimp [liftBox]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [t.property.1, t.property.2]
  · rw [diagonal_formula]
    dsimp
    linarith

/-- The diagonal's actual image is the existing embedded (1,1) affine circle,
with complementary column (0,1), half offset, and parameter shifted by 3/4. -/
theorem surgeryDiagonalLift_projection_affine (t : unitInterval) :
    surgeryPlaneProjection (surgeryDiagonalLift t) =
      (standardPuncturedAffineCircle (1,1) (0,1) (by norm_num [intDet])
        standardCircleHalf standardCircleHalf_ne_zero
          ((((3/4 : ℝ) : AddCircle (1 : ℝ))) + ((t : ℝ) : AddCircle (1 : ℝ)))).val := by
  rw [diagonal_formula]
  apply Prod.ext
  · change (((3/4+(t : ℝ) : ℝ)) : AddCircle (1 : ℝ)) =
      (1 : ℤ) • ((((3/4 : ℝ) : AddCircle (1 : ℝ))) + ((t : ℝ) : AddCircle (1 : ℝ))) +
        (0 : ℤ) • standardCircleHalf
    simp only [one_zsmul, zero_zsmul, add_zero]
    rfl
  · change (((1/4+(t : ℝ) : ℝ)) : AddCircle (1 : ℝ)) =
      (1 : ℤ) • ((((3/4 : ℝ) : AddCircle (1 : ℝ))) + ((t : ℝ) : AddCircle (1 : ℝ))) +
        (1 : ℤ) • standardCircleHalf
    simp only [one_zsmul]
    change (((1/4+(t : ℝ) : ℝ)) : AddCircle (1 : ℝ)) =
      (((3/4+(t : ℝ)+1/2 : ℝ)) : AddCircle (1 : ℝ))
    have h : 3/4+(t : ℝ)+1/2 = (1/4+(t : ℝ))+1 := by ring
    rw [h, AddCircle.coe_add_period]

/-- The actual diagonal-loop basepoint is the class of (3/4,1/4). -/
def surgeryDiagonalBasePoint : StandardPuncturedTorus :=
  ⟨surgeryPlaneProjection surgeryDiagonalStartLift, by
    simpa only [surgeryDiagonalLift.source] using diagonal_avoids 0⟩

private theorem diagonal_end_projection : surgeryPlaneProjection surgeryDiagonalEndLift =
    surgeryPlaneProjection surgeryDiagonalStartLift := by
  apply Prod.ext
  · change ((7/4 : ℝ) : AddCircle (1 : ℝ)) = ((3/4 : ℝ) : AddCircle (1 : ℝ))
    convert AddCircle.coe_add_period (p := (1 : ℝ)) (3/4 : ℝ) using 1
    norm_num
  · change ((5/4 : ℝ) : AddCircle (1 : ℝ)) = ((1/4 : ℝ) : AddCircle (1 : ℝ))
    convert AddCircle.coe_add_period (p := (1 : ℝ)) (1/4 : ℝ) using 1
    norm_num

/-- The actual short connecting path to the embedded diagonal circle. -/
def surgeryConnector : Path surgeryBasePoint surgeryDiagonalBasePoint where
  toFun t := ⟨surgeryPlaneProjection (surgeryConnectorLift t), connector_avoids t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact projection_continuous.comp surgeryConnectorLift.continuous
  source' := by apply Subtype.ext; exact congrArg surgeryPlaneProjection surgeryConnectorLift.source
  target' := by apply Subtype.ext; exact congrArg surgeryPlaneProjection surgeryConnectorLift.target

/-- The actual once-around diagonal loop, with its embedded affine image identified above. -/
def surgeryDiagonalLoop : Path surgeryDiagonalBasePoint surgeryDiagonalBasePoint where
  toFun t := ⟨surgeryPlaneProjection (surgeryDiagonalLift t), diagonal_avoids t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact projection_continuous.comp surgeryDiagonalLift.continuous
  source' := by apply Subtype.ext; exact congrArg surgeryPlaneProjection surgeryDiagonalLift.source
  target' := by
    apply Subtype.ext
    exact (congrArg surgeryPlaneProjection surgeryDiagonalLift.target).trans diagonal_end_projection

/-- The target loop has exactly the stated actual connector–diagonal–reverse-connector form. -/
theorem surgerySmoothedLoop_eq_connector_diagonal_reverse :
    surgerySmoothedLoop = (surgeryConnector.trans surgeryDiagonalLoop).trans surgeryConnector.symm := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change surgeryPlaneProjection (surgerySmoothedLift t) = _
  simp only [surgerySmoothedLift, Path.trans_apply]
  split_ifs
  · rfl
  · rfl
  · change surgeryPlaneProjection (surgeryReturnLift _) =
      surgeryPlaneProjection (surgeryConnectorLift.symm _)
    rw [surgeryReturnLift_eq_translated_reverse]
    apply Prod.ext
    · exact AddCircle.coe_add_period (p := (1 : ℝ)) _
    · exact AddCircle.coe_add_period (p := (1 : ℝ)) _

/-- Concrete positive mediant surgery in the actual punctured torus: the
positive horizontal-vertical product is genuinely based homotopic to a
connector followed by the actual embedded diagonal loop and connector reversal. -/
theorem surgeryPositiveProduct_homotopic_embeddedDiagonal :
    (surgeryHorizontalLoop.trans surgeryVerticalLoop).Homotopic
      ((surgeryConnector.trans surgeryDiagonalLoop).trans surgeryConnector.symm) := by
  rw [← surgerySmoothedLoop_eq_connector_diagonal_reverse]
  exact surgeryHorizontal_trans_vertical_homotopic

end Markov
