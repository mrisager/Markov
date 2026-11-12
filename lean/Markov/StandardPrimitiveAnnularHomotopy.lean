import Markov.StandardAffineComplementCylinder
import Markov.FilledTorusCircleHomotopy

/-! Actual primitive through-zero circle complements and their puncture-preserving
annular homotopies. Containment in the annulus is an explicit geometric hypothesis;
no arbitrary embedded-curve normal form is asserted. -/

noncomputable section
open Set Topology
namespace Markov

/-- The actual determinant-one torus map identifies the horizontal through-zero
complement with the actual primitive dual-coordinate nonzero set. -/
def standardPrimitiveZeroComplementHomeomorph
    (p q : ℤ × ℤ) (hpq : intDet p q = 1) :
    {z : StandardTorus // z.2 ≠ 0} ≃ₜ
      {z : StandardTorus // standardTorusSecondDual p z ≠ 0} :=
  (standardUnimodularTorusHomeomorph p q hpq).subtype (fun z => by
    have he : standardTorusSecondDual p
        (standardUnimodularTorusHomeomorph p q hpq z) = z.2 :=
      (standardTorusSecondDual_integerCombination p q z.1 z.2).trans
        (by rw [hpq, one_smul])
    rw [he])

/-- The removed primitive affine circle passes through the literal puncture,
so its actual complement includes continuously into the punctured torus. -/
def standardPrimitiveZeroComplementInclusion (p : ℤ × ℤ) :
    C({z : StandardTorus // standardTorusSecondDual p z ≠ 0}, StandardPuncturedTorus) where
  toFun z := ⟨z.val, by
    intro he
    apply z.property
    rw [he]
    simp [standardTorusSecondDual]⟩
  continuous_toFun := by fun_prop

/-- The literal longitudinal coordinate in the checked unimodular chart. -/
def standardPrimitiveZeroComplementLongitudinal
    (p q : ℤ × ℤ) (hpq : intDet p q = 1) :
    C({z : StandardTorus // standardTorusSecondDual p z ≠ 0}, NormalizedCircle) where
  toFun z := ((standardPrimitiveZeroComplementHomeomorph p q hpq).symm z).val.1
  continuous_toFun := by fun_prop

/-- An actual fixed parallel circle inside the primitive through-zero complement. -/
def standardPrimitiveZeroComplementParallel
    (p q : ℤ × ℤ) (hpq : intDet p q = 1) :
    C(NormalizedCircle, {z : StandardTorus // standardTorusSecondDual p z ≠ 0}) where
  toFun u := standardPrimitiveZeroComplementHomeomorph p q hpq
    ⟨(u, (normalizedCircleCutHomeomorph 0 ⟨1 / 2, by norm_num⟩).val),
      (normalizedCircleCutHomeomorph 0 ⟨1 / 2, by norm_num⟩).property⟩
  continuous_toFun := by
    apply (standardPrimitiveZeroComplementHomeomorph p q hpq).continuous.comp
    apply Continuous.subtype_mk
    exact continuous_id.prodMk continuous_const

/-- The actual retraction is transported through the actual unimodular homeomorphism. -/
def standardPrimitiveZeroComplementRetract
    (p q : ℤ × ℤ) (hpq : intDet p q = 1) :
    C({z : StandardTorus // standardTorusSecondDual p z ≠ 0},
      {z : StandardTorus // standardTorusSecondDual p z ≠ 0}) :=
  (standardPrimitiveZeroComplementParallel p q hpq).comp
    (standardPrimitiveZeroComplementLongitudinal p q hpq)

/-- The primitive through-zero complement has an actual identity-to-parallel
retraction homotopy, hence it avoids the puncture at every intermediate time. -/
def standardPrimitiveZeroComplementDeformation
    (p q : ℤ × ℤ) (hpq : intDet p q = 1) :
    (ContinuousMap.id {z : StandardTorus // standardTorusSecondDual p z ≠ 0}).Homotopy
      (standardPrimitiveZeroComplementRetract p q hpq) := by
  let e := standardPrimitiveZeroComplementHomeomorph p q hpq
  let H := (ContinuousMap.Homotopy.refl ⟨e, e.continuous⟩).comp
    ((standardHorizontalComplementDeformation 0).compContinuousMap ⟨e.symm, e.symm.continuous⟩)
  apply H.cast
  · apply ContinuousMap.ext
    intro z
    exact e.apply_symm_apply z
  · apply ContinuousMap.ext
    intro z
    rfl

/-- The actual retraction factors through the literal longitudinal coordinate
and the actual parallel circle, without a classification premise. -/
theorem standardPrimitiveZeroComplementRetract_eq_parallel_comp
    (p q : ℤ × ℤ) (hpq : intDet p q = 1) :
    standardPrimitiveZeroComplementRetract p q hpq =
      (standardPrimitiveZeroComplementParallel p q hpq).comp
        (standardPrimitiveZeroComplementLongitudinal p q hpq) := by
  rfl

/-- Within an actual primitive through-zero annulus, equality of genuine
longitudinal cover winding gives an actual circle-map homotopy in that annulus. -/
theorem standardPrimitiveZeroComplement_homotopic_of_longitudinal_winding_eq
    (p q : ℤ × ℤ) (hpq : intDet p q = 1)
    (f g : C(NormalizedCircle, {z : StandardTorus // standardTorusSecondDual p z ≠ 0}))
    (hw : normalizedCircleMapWinding
        ((standardPrimitiveZeroComplementLongitudinal p q hpq).comp f) =
      normalizedCircleMapWinding
        ((standardPrimitiveZeroComplementLongitudinal p q hpq).comp g)) : f.Homotopic g := by
  have hf : f.Homotopic ((standardPrimitiveZeroComplementRetract p q hpq).comp f) := by
    exact ⟨(standardPrimitiveZeroComplementDeformation p q hpq).compContinuousMap f⟩
  have hg : g.Homotopic ((standardPrimitiveZeroComplementRetract p q hpq).comp g) := by
    exact ⟨(standardPrimitiveZeroComplementDeformation p q hpq).compContinuousMap g⟩
  have hh := (ContinuousMap.Homotopic.refl
      (standardPrimitiveZeroComplementParallel p q hpq)).comp
    (normalizedCircleMap_homotopic_of_winding_eq _ _ hw)
  have hm : ((standardPrimitiveZeroComplementRetract p q hpq).comp f).Homotopic
      ((standardPrimitiveZeroComplementRetract p q hpq).comp g) := by
    exact hh
  exact hf.trans (hm.trans hg.symm)

/-- The annular classification above is a genuine homotopy in the actual
punctured torus after the literal inclusion, not just a filled-torus homotopy. -/
theorem standardPrimitiveZeroComplement_punctured_homotopic_of_longitudinal_winding_eq
    (p q : ℤ × ℤ) (hpq : intDet p q = 1)
    (f g : C(NormalizedCircle, {z : StandardTorus // standardTorusSecondDual p z ≠ 0}))
    (hw : normalizedCircleMapWinding
        ((standardPrimitiveZeroComplementLongitudinal p q hpq).comp f) =
      normalizedCircleMapWinding
        ((standardPrimitiveZeroComplementLongitudinal p q hpq).comp g)) :
    ((standardPrimitiveZeroComplementInclusion p).comp f).Homotopic
      ((standardPrimitiveZeroComplementInclusion p).comp g) :=
  (ContinuousMap.Homotopic.refl (standardPrimitiveZeroComplementInclusion p)).comp
    (standardPrimitiveZeroComplement_homotopic_of_longitudinal_winding_eq p q hpq f g hw)

end Markov
