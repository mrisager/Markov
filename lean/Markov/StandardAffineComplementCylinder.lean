import Markov.StandardAffineCircleComplement
import Mathlib.Topology.Homotopy.Basic

/-! An actual cylinder chart and strong deformation in the FILLED torus minus
a coordinate circle. This does not put an arbitrary embedded curve into that
chart and does not claim to preserve the additional torus puncture at zero. -/

noncomputable section
open Set Topology
namespace Markov

/-- Translation carries the literal zero-punctured circle to the complement
of an arbitrary actual circle point. -/
def normalizedCircleTranslateComplementHomeomorph (c : NormalizedCircle) :
    {z : NormalizedCircle // z ≠ 0} ≃ₜ {z : NormalizedCircle // z ≠ c} where
  toFun z := ⟨z.val + c, by
    intro he
    apply z.property
    simpa using congrArg (fun w : NormalizedCircle => w - c) he⟩
  invFun z := ⟨z.val - c, sub_ne_zero.mpr z.property⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The actual normalized circle cut at c is homeomorphic to the open unit
interval, using the pinned quotient chart and actual translation. -/
def normalizedCircleCutHomeomorph (c : NormalizedCircle) :
    Set.Ioo (0 : ℝ) 1 ≃ₜ {z : NormalizedCircle // z ≠ c} := by
  let e := AddCircle.openPartialHomeomorphCoe (1 : ℝ) (0 : ℝ)
  have hs : e.source = Set.Ioo (0 : ℝ) 1 := by simp [e, AddCircle.openPartialHomeomorphCoe]
  have ht : e.target = {z : NormalizedCircle | z ≠ 0} := by
    ext z
    simp [e, AddCircle.openPartialHomeomorphCoe]
  exact ((Homeomorph.setCongr hs.symm).trans
    (e.toHomeomorphSourceTarget.trans (Homeomorph.setCongr ht))).trans
      (normalizedCircleTranslateComplementHomeomorph c)

/-- A literal cylinder homeomorphism onto the filled horizontal-circle
complement; both maps and inverse laws are actual maps of the existing sets. -/
def standardHorizontalComplementCylinderHomeomorph (c : NormalizedCircle) :
    (NormalizedCircle × Set.Ioo (0 : ℝ) 1) ≃ₜ {z : StandardTorus // z.2 ≠ c} where
  toFun z := ⟨(z.1, (normalizedCircleCutHomeomorph c z.2).val),
    (normalizedCircleCutHomeomorph c z.2).property⟩
  invFun z := (z.val.1, (normalizedCircleCutHomeomorph c).symm ⟨z.val.2, z.property⟩)
  left_inv z := by
    apply Prod.ext
    · rfl
    · exact (normalizedCircleCutHomeomorph c).symm_apply_apply z.2
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        ((normalizedCircleCutHomeomorph c).apply_symm_apply ⟨z.val.2, z.property⟩)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def cylinderMidpoint : Set.Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩

private def cylinderShrink (s : unitInterval) (x : Set.Ioo (0 : ℝ) 1) : Set.Ioo (0 : ℝ) 1 :=
  ⟨(1 - (s : ℝ)) * (x : ℝ) + (s : ℝ) * (1 / 2), by
    simpa only [smul_eq_mul] using
      (convex_iff_add_mem.mp (convex_Ioo (0 : ℝ) 1)) x.property
        (show (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 by norm_num)
        (sub_nonneg.mpr s.property.2) s.property.1 (by ring)⟩

private theorem cylinderShrink_zero (x : Set.Ioo (0 : ℝ) 1) : cylinderShrink 0 x = x := by
  apply Subtype.ext
  simp [cylinderShrink]

private theorem cylinderShrink_one (x : Set.Ioo (0 : ℝ) 1) :
    cylinderShrink 1 x = cylinderMidpoint := by
  apply Subtype.ext
  simp [cylinderShrink, cylinderMidpoint]

private theorem cylinderShrink_midpoint (s : unitInterval) :
    cylinderShrink s cylinderMidpoint = cylinderMidpoint := by
  apply Subtype.ext
  dsimp [cylinderShrink, cylinderMidpoint]
  ring

private theorem continuous_cylinderShrink :
    Continuous (fun z : unitInterval × Set.Ioo (0 : ℝ) 1 => cylinderShrink z.1 z.2) := by
  apply Continuous.subtype_mk
  fun_prop

private def horizontalCylinderCoordinate (c : NormalizedCircle)
    (z : {z : StandardTorus // z.2 ≠ c}) : Set.Ioo (0 : ℝ) 1 :=
  (normalizedCircleCutHomeomorph c).symm ⟨z.val.2, z.property⟩

private theorem continuous_horizontalCylinderCoordinate (c : NormalizedCircle) :
    Continuous (horizontalCylinderCoordinate c) := by
  unfold horizontalCylinderCoordinate
  fun_prop

/-- An actual retraction onto a fixed parallel circle in the filled
horizontal complement, preserving the first circle coordinate pointwise. -/
def standardHorizontalComplementRetract (c : NormalizedCircle) :
    C({z : StandardTorus // z.2 ≠ c}, {z : StandardTorus // z.2 ≠ c}) where
  toFun z := ⟨(z.val.1, (normalizedCircleCutHomeomorph c cylinderMidpoint).val),
    (normalizedCircleCutHomeomorph c cylinderMidpoint).property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk continuous_const

theorem standardHorizontalComplementRetract_idem (c : NormalizedCircle)
    (z : {z : StandardTorus // z.2 ≠ c}) :
    standardHorizontalComplementRetract c (standardHorizontalComplementRetract c z) =
      standardHorizontalComplementRetract c z := rfl

/-- The image of the actual retraction is exactly its stated parallel
circle fibre, rather than an abstract retract supplied by a field. -/
theorem standardHorizontalComplementRetract_range (c : NormalizedCircle) :
    Set.range (standardHorizontalComplementRetract c) =
      {z : {z : StandardTorus // z.2 ≠ c} |
        z.val.2 = (normalizedCircleCutHomeomorph c ⟨1 / 2, by norm_num⟩).val} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro hz
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl hz.symm

/-- Explicit strong deformation from the actual filled horizontal-complement
identity to that retraction, by linear interpolation in the actual cut chart. -/
def standardHorizontalComplementDeformation (c : NormalizedCircle) :
    (ContinuousMap.id {z : StandardTorus // z.2 ≠ c}).Homotopy
      (standardHorizontalComplementRetract c) where
  toFun z :=
    ⟨(z.2.val.1, (normalizedCircleCutHomeomorph c
      (cylinderShrink z.1 (horizontalCylinderCoordinate c z.2))).val),
      (normalizedCircleCutHomeomorph c
        (cylinderShrink z.1 (horizontalCylinderCoordinate c z.2))).property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
      (continuous_subtype_val.comp ((normalizedCircleCutHomeomorph c).continuous.comp
        (continuous_cylinderShrink.comp (continuous_fst.prodMk
          ((continuous_horizontalCylinderCoordinate c).comp continuous_snd)))))
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (normalizedCircleCutHomeomorph c
        (cylinderShrink 0 (horizontalCylinderCoordinate c z))).val = z.val.2
      rw [cylinderShrink_zero]
      exact congrArg Subtype.val
        ((normalizedCircleCutHomeomorph c).apply_symm_apply ⟨z.val.2, z.property⟩)
  map_one_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (normalizedCircleCutHomeomorph c
        (cylinderShrink 1 (horizontalCylinderCoordinate c z))).val =
          (normalizedCircleCutHomeomorph c cylinderMidpoint).val
      rw [cylinderShrink_one]

/-- The explicit deformation fixes every point of its actual retraction
image throughout, including the original first coordinate. -/
theorem standardHorizontalComplementDeformation_fix_retract (c : NormalizedCircle)
    (s : unitInterval) (z : {z : StandardTorus // z.2 ≠ c}) :
    standardHorizontalComplementDeformation c (s, standardHorizontalComplementRetract c z) =
      standardHorizontalComplementRetract c z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (normalizedCircleCutHomeomorph c
      (cylinderShrink s ((normalizedCircleCutHomeomorph c).symm
        (normalizedCircleCutHomeomorph c cylinderMidpoint)))).val =
      (normalizedCircleCutHomeomorph c cylinderMidpoint).val
    rw [Homeomorph.symm_apply_apply, cylinderShrink_midpoint]

end Markov
