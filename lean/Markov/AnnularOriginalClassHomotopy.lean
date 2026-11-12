import Markov.NormalizedCircleWindingLinear
import Markov.StandardPrimitiveAnnularHomotopy
import Markov.ModularOriginalPrimitiveCircles

noncomputable section
open Set Topology
namespace Markov

/-- The literal inclusion of the actual primitive through-zero annulus in
the actual modular punctured torus. -/
def standardPrimitiveAnnulusModularInclusion (r : ℤ × ℤ) :
    C({z : StandardTorus // standardTorusSecondDual r z ≠ 0}, ModularTraceQuotient) :=
  ⟨fun z => modularTraceQuotientPuncturedTorusHomeomorph.symm
    (standardPrimitiveZeroComplementInclusion r z), by fun_prop⟩

/-- The already checked genuine original marking computes exactly the two
covering windings of a literal actual modular circle map. -/
theorem modularCircleMap_standard_winding (q : C(NormalizedCircle, ModularTraceQuotient)) :
    standardTorusCircleMapWinding
      ⟨fun u => (modularTraceQuotientPuncturedTorusHomeomorph (q u)).val,
        continuous_subtype_val.comp
          (modularTraceQuotientPuncturedTorusHomeomorph.continuous.comp q.continuous)⟩ =
      originalToStandardCircleLabel (modularTraceFixedSingularH1Equiv
        (singularLoopClass ModularTraceQuotient (normalizedCircleStandardLoop.map q.continuous))) := by
  change modularStandardLoopWinding (normalizedCircleStandardLoop.map q.continuous) = _
  exact (modularStandardH1Winding_loop _).symm.trans
    (modularStandardH1Winding_fixedCoordinates _)

/-- Literal longitudinal coordinate of the actual unimodular annulus chart. -/
theorem standardPrimitiveZeroComplementLongitudinal_apply
    (r a : ℤ × ℤ) (ha : intDet r a = 1)
    (z : {z : StandardTorus // standardTorusSecondDual r z ≠ 0}) :
    standardPrimitiveZeroComplementLongitudinal r a ha z = standardTorusFirstDual a z.val := rfl

/-- WITH actual annulus containment, the prescribed original H1 class gives
genuine longitudinal covering winding one in the actual determinant-one chart. -/
theorem standardPrimitiveAnnulus_longitudinal_winding_eq_one
    (p a : ℤ × ℤ) (ha : intDet (originalToStandardCircleLabel p) a = 1)
    (f : C(NormalizedCircle,
      {z : StandardTorus // standardTorusSecondDual (originalToStandardCircleLabel p) z ≠ 0}))
    (hclass : modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient
        (normalizedCircleStandardLoop.map
          ((standardPrimitiveAnnulusModularInclusion (originalToStandardCircleLabel p)).comp f).continuous)) = p) :
    normalizedCircleMapWinding
      ((standardPrimitiveZeroComplementLongitudinal (originalToStandardCircleLabel p) a ha).comp f) = 1 := by
  let Q := (standardPrimitiveAnnulusModularInclusion (originalToStandardCircleLabel p)).comp f
  let T : C(NormalizedCircle, StandardTorus) := ⟨fun u => (f u).val, by fun_prop⟩
  have he : (⟨fun u => (modularTraceQuotientPuncturedTorusHomeomorph (Q u)).val,
      continuous_subtype_val.comp
        (modularTraceQuotientPuncturedTorusHomeomorph.continuous.comp Q.continuous)⟩ :
      C(NormalizedCircle, StandardTorus)) = T := by
    ext u <;>
      simp [Q, standardPrimitiveAnnulusModularInclusion, standardPrimitiveZeroComplementInclusion,
      T, Homeomorph.apply_symm_apply]
  have hw := modularCircleMap_standard_winding Q
  have hQ : modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient (normalizedCircleStandardLoop.map Q.continuous)) = p := hclass
  rw [he, hQ] at hw
  have hlong : (standardPrimitiveZeroComplementLongitudinal
      (originalToStandardCircleLabel p) a ha).comp f =
      ⟨fun u => standardTorusFirstDual a (T u),
        (continuous_standardTorusFirstDual a).comp T.continuous⟩ := by
    ext u
    rfl
  rw [hlong, standardTorusCircleMap_firstDual_winding, hw]
  change a.2*(originalToStandardCircleLabel p).1 - a.1*(originalToStandardCircleLabel p).2 = 1
  change (originalToStandardCircleLabel p).1*a.2 -
    (originalToStandardCircleLabel p).2*a.1 = 1 at ha
  nlinarith [ha]

/-- A literal affine parallel circle inside the actual primitive annulus,
with arbitrary actual nonzero transverse offset. -/
def standardPrimitiveAnnulusAffineMap (r a : ℤ × ℤ) (ha : intDet r a = 1)
    (c : NormalizedCircle) (hc : c ≠ 0) :
    C(NormalizedCircle, {z : StandardTorus // standardTorusSecondDual r z ≠ 0}) where
  toFun u := ⟨standardTorusIntegerCombination r a u c, by
    rw [standardTorusSecondDual_integerCombination, ha, one_smul]
    exact hc⟩
  continuous_toFun := by unfold standardTorusIntegerCombination; fun_prop

theorem standardPrimitiveAnnulusAffineMap_longitudinal_winding
    (r a : ℤ × ℤ) (ha : intDet r a = 1) (c : NormalizedCircle) (hc : c ≠ 0) :
    normalizedCircleMapWinding ((standardPrimitiveZeroComplementLongitudinal r a ha).comp
      (standardPrimitiveAnnulusAffineMap r a ha c hc)) = 1 := by
  have he : (standardPrimitiveZeroComplementLongitudinal r a ha).comp
      (standardPrimitiveAnnulusAffineMap r a ha c hc) = ContinuousMap.id NormalizedCircle := by
    ext u
    change standardTorusFirstDual a (standardTorusIntegerCombination r a u c) = u
    exact (standardTorusFirstDual_integerCombination r a u c).trans (by rw [ha, one_smul])
  rw [he]
  have hp : normalizedCircleTranslatedLoop
      (normalizedCircleStandardLoop.map (ContinuousMap.id NormalizedCircle).continuous) =
      normalizedCircleStandardLoop := by
    ext t
    simp [normalizedCircleTranslatedLoop]
  change normalizedCircleWinding _ = 1
  rw [hp, normalizedCircleWinding_standardLoop]

/-- The actual annular theorem, with its genuine winding hypothesis now
discharged from the original H1 marking, gives an actual punctured-torus map
homotopy to the literal affine circle. Containment remains explicit. -/
theorem standardPrimitiveAnnulus_homotopic_affine_of_original_H1
    (p a : ℤ × ℤ) (ha : intDet (originalToStandardCircleLabel p) a = 1)
    (f : C(NormalizedCircle,
      {z : StandardTorus // standardTorusSecondDual (originalToStandardCircleLabel p) z ≠ 0}))
    (hclass : modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient
        (normalizedCircleStandardLoop.map
          ((standardPrimitiveAnnulusModularInclusion (originalToStandardCircleLabel p)).comp f).continuous)) = p)
    (c : NormalizedCircle) (hc : c ≠ 0) :
    ((standardPrimitiveAnnulusModularInclusion (originalToStandardCircleLabel p)).comp f).Homotopic
      ⟨modularAffineCircle (originalToStandardCircleLabel p) a ha c hc,
        continuous_modularAffineCircle _ _ _ _ _⟩ := by
  have hw := (standardPrimitiveAnnulus_longitudinal_winding_eq_one p a ha f hclass).trans
    (standardPrimitiveAnnulusAffineMap_longitudinal_winding
      (originalToStandardCircleLabel p) a ha c hc).symm
  have hh := standardPrimitiveZeroComplement_homotopic_of_longitudinal_winding_eq
    (originalToStandardCircleLabel p) a ha f
    (standardPrimitiveAnnulusAffineMap (originalToStandardCircleLabel p) a ha c hc) hw
  have hi := (ContinuousMap.Homotopic.refl
    (standardPrimitiveAnnulusModularInclusion (originalToStandardCircleLabel p))).comp hh
  have he : (standardPrimitiveAnnulusModularInclusion (originalToStandardCircleLabel p)).comp
      (standardPrimitiveAnnulusAffineMap (originalToStandardCircleLabel p) a ha c hc) =
      ⟨modularAffineCircle (originalToStandardCircleLabel p) a ha c hc,
        continuous_modularAffineCircle _ _ _ _ _⟩ := by ext u; rfl
  rwa [he] at hi

/-- An ACTUALLY contained modular circle map with original H1=p is genuinely
homotopic to the actual affine circle, within the punctured torus. -/
theorem modularCircleMap_homotopic_affine_of_annular_containment
    (p a : ℤ × ℤ) (ha : intDet (originalToStandardCircleLabel p) a = 1)
    (q : C(NormalizedCircle, ModularTraceQuotient))
    (hcontain : ∀ u, standardTorusSecondDual (originalToStandardCircleLabel p)
      (modularTraceQuotientPuncturedTorusHomeomorph (q u)).val ≠ 0)
    (hclass : modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient (normalizedCircleStandardLoop.map q.continuous)) = p)
    (c : NormalizedCircle) (hc : c ≠ 0) :
    q.Homotopic ⟨modularAffineCircle (originalToStandardCircleLabel p) a ha c hc,
      continuous_modularAffineCircle _ _ _ _ _⟩ := by
  let f : C(NormalizedCircle,
      {z : StandardTorus // standardTorusSecondDual (originalToStandardCircleLabel p) z ≠ 0}) :=
    ⟨fun u => ⟨(modularTraceQuotientPuncturedTorusHomeomorph (q u)).val, hcontain u⟩, by fun_prop⟩
  have he : (standardPrimitiveAnnulusModularInclusion (originalToStandardCircleLabel p)).comp f = q := by
    ext u
    change modularTraceQuotientPuncturedTorusHomeomorph.symm
      (modularTraceQuotientPuncturedTorusHomeomorph (q u)) = q u
    exact Homeomorph.symm_apply_apply _ _
  have hfc : modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient (normalizedCircleStandardLoop.map
        ((standardPrimitiveAnnulusModularInclusion (originalToStandardCircleLabel p)).comp f).continuous)) = p := by
    rw [he]
    exact hclass
  have hh := standardPrimitiveAnnulus_homotopic_affine_of_original_H1 p a ha f hfc c hc
  rwa [he] at hh

end Markov
