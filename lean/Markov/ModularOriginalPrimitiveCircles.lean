import Markov.ModularAffineCircleCoordinates
import Markov.NormalizedCircleWindingConjugation

noncomputable section
open Topology
namespace Markov

/-- A genuine singular-H1 detector evaluates at an arbitrary loop basepoint,
using the proved actual conjugation identity and genuine circle winding. -/
theorem singularH1CircleWinding_loop_arbitrary
    {X : Type} [TopologicalSpace X] (x : X) (τ : ∀ z : X, Path x z)
    (r : X → NormalizedCircle) (hr : Continuous r) (hrx : r x = 0)
    {y : X} (γ : Path y y) :
    singularH1CircleWinding x τ r hr hrx (singularLoopClass X γ) =
      normalizedCircleWinding (normalizedCircleTranslatedLoop (γ.map hr)) := by
  rw [← singularLoopClass_conjugate X (τ y) γ, singularH1CircleWinding_loop]
  let η := ((τ y).trans γ).trans (τ y).symm
  have hcast : ((η.map hr).cast hrx.symm hrx.symm) =
      normalizedCircleTranslatedLoop (η.map hr) := by
    ext t
    change r (η t) = r (η t) - r x
    rw [hrx, sub_zero]
  change normalizedCircleWinding ((η.map hr).cast hrx.symm hrx.symm) = _
  rw [hcast]
  have hmap : η.map hr = (((τ y).map hr).trans (γ.map hr)).trans
      ((τ y).map hr).symm := by
    simp only [η, Path.map_trans, Path.map_symm]
  rw [hmap, normalizedCircleWinding_translated_conjugate]

/-- Actual first standard circle coordinate of the actual quotient homeomorphism. -/
def modularStandardFirstCoordinate (z : ModularTraceQuotient) : NormalizedCircle :=
  (modularTraceQuotientPuncturedTorusHomeomorph z).val.1

/-- Actual second standard circle coordinate of the actual quotient homeomorphism. -/
def modularStandardSecondCoordinate (z : ModularTraceQuotient) : NormalizedCircle :=
  (modularTraceQuotientPuncturedTorusHomeomorph z).val.2

theorem continuous_modularStandardFirstCoordinate : Continuous modularStandardFirstCoordinate :=
  continuous_fst.comp (continuous_subtype_val.comp
    modularTraceQuotientPuncturedTorusHomeomorph.continuous)

theorem continuous_modularStandardSecondCoordinate : Continuous modularStandardSecondCoordinate :=
  continuous_snd.comp (continuous_subtype_val.comp
    modularTraceQuotientPuncturedTorusHomeomorph.continuous)

/-- The first genuine actual singular-H1 winding homomorphism uses fixed I
and subtracts the first coordinate there. -/
def modularStandardFirstH1Winding : integralSingularH1 ModularTraceQuotient →+ ℤ :=
  singularH1CircleWinding (modularTraceQuotientMk UpperHalfPlane.I)
    (modularTraceSingularConnector UpperHalfPlane.I)
    (fun z => modularStandardFirstCoordinate z -
      modularStandardFirstCoordinate (modularTraceQuotientMk UpperHalfPlane.I))
    (continuous_modularStandardFirstCoordinate.sub continuous_const)
    (sub_self _)

/-- The second genuine actual singular-H1 winding homomorphism uses fixed I
and subtracts the second coordinate there. -/
def modularStandardSecondH1Winding : integralSingularH1 ModularTraceQuotient →+ ℤ :=
  singularH1CircleWinding (modularTraceQuotientMk UpperHalfPlane.I)
    (modularTraceSingularConnector UpperHalfPlane.I)
    (fun z => modularStandardSecondCoordinate z -
      modularStandardSecondCoordinate (modularTraceQuotientMk UpperHalfPlane.I))
    (continuous_modularStandardSecondCoordinate.sub continuous_const)
    (sub_self _)

/-- Exact first detector evaluation at every actual quotient loop basepoint. -/
theorem modularStandardFirstH1Winding_loop {x : ModularTraceQuotient} (γ : Path x x) :
    modularStandardFirstH1Winding (singularLoopClass ModularTraceQuotient γ) =
      (modularStandardLoopWinding γ).1 := by
  unfold modularStandardFirstH1Winding
  rw [singularH1CircleWinding_loop_arbitrary]
  apply congrArg normalizedCircleWinding
  ext t
  change (modularStandardFirstCoordinate (γ t) -
      modularStandardFirstCoordinate (modularTraceQuotientMk UpperHalfPlane.I)) -
    (modularStandardFirstCoordinate x -
      modularStandardFirstCoordinate (modularTraceQuotientMk UpperHalfPlane.I)) =
    modularStandardFirstCoordinate (γ t) - modularStandardFirstCoordinate x
  abel

/-- Exact second detector evaluation at every actual quotient loop basepoint. -/
theorem modularStandardSecondH1Winding_loop {x : ModularTraceQuotient} (γ : Path x x) :
    modularStandardSecondH1Winding (singularLoopClass ModularTraceQuotient γ) =
      (modularStandardLoopWinding γ).2 := by
  unfold modularStandardSecondH1Winding
  rw [singularH1CircleWinding_loop_arbitrary]
  apply congrArg normalizedCircleWinding
  ext t
  change (modularStandardSecondCoordinate (γ t) -
      modularStandardSecondCoordinate (modularTraceQuotientMk UpperHalfPlane.I)) -
    (modularStandardSecondCoordinate x -
      modularStandardSecondCoordinate (modularTraceQuotientMk UpperHalfPlane.I)) =
    modularStandardSecondCoordinate (γ t) - modularStandardSecondCoordinate x
  abel

/-- Pairing the two genuine winding detectors gives an actual homomorphism on actual H1. -/
def modularStandardH1Winding : integralSingularH1 ModularTraceQuotient →+ (ℤ × ℤ) :=
  modularStandardFirstH1Winding.prod modularStandardSecondH1Winding

theorem modularStandardH1Winding_loop {x : ModularTraceQuotient} (γ : Path x x) :
    modularStandardH1Winding (singularLoopClass ModularTraceQuotient γ) =
      modularStandardLoopWinding γ := by
  apply Prod.ext
  · exact modularStandardFirstH1Winding_loop γ
  · exact modularStandardSecondH1Winding_loop γ

/-- Evaluation on the concrete original positive A loop is proved from its actual mapped path. -/
theorem modularStandardH1Winding_generatorA :
    modularStandardH1Winding
      (singularLoopClass ModularTraceQuotient paperSquareAOriginalLoop) = ((0, -1) : ℤ × ℤ) := by
  rw [modularStandardH1Winding_loop]
  exact paperSquareAOriginalLoop_standardWinding

/-- Evaluation on the concrete original positive B loop is proved from its actual mapped path. -/
theorem modularStandardH1Winding_generatorB :
    modularStandardH1Winding
      (singularLoopClass ModularTraceQuotient paperSquareBOriginalLoop) = ((-1, 0) : ℤ × ℤ) := by
  rw [modularStandardH1Winding_loop]
  exact paperSquareBOriginalLoop_standardWinding

/-- The genuine winding detector pair is the signed interchange of the proved
original fixed-I singular-H1 coordinates, on every actual homology class. -/
theorem modularStandardH1Winding_fixedCoordinates
    (c : integralSingularH1 ModularTraceQuotient) :
    modularStandardH1Winding c =
      originalToStandardCircleLabel (modularTraceFixedSingularH1Equiv c) := by
  let a := singularLoopClass ModularTraceQuotient paperSquareAOriginalLoop
  let b := singularLoopClass ModularTraceQuotient paperSquareBOriginalLoop
  have ha : modularTraceFixedSingularH1Equiv a = ((1, 0) : ℤ × ℤ) :=
    paperSquareAOriginalLoop_fixedH1
  have hb : modularTraceFixedSingularH1Equiv b = ((0, 1) : ℤ × ℤ) :=
    paperSquareBOriginalLoop_fixedH1
  have hd : c = (modularTraceFixedSingularH1Equiv c).1 • a +
      (modularTraceFixedSingularH1Equiv c).2 • b := by
    apply modularTraceFixedSingularH1Equiv.injective
    rw [map_add, map_zsmul, map_zsmul, ha, hb]
    ext <;> simp
  rw [hd, map_add, map_zsmul, map_zsmul]
  change _ = originalToStandardCircleLabel
    (modularTraceFixedSingularH1Equiv
      ((modularTraceFixedSingularH1Equiv c).1 • a +
        (modularTraceFixedSingularH1Equiv c).2 • b))
  rw [map_add, map_zsmul, map_zsmul, ha, hb]
  change (modularTraceFixedSingularH1Equiv c).1 • modularStandardH1Winding a +
    (modularTraceFixedSingularH1Equiv c).2 • modularStandardH1Winding b = _
  rw [show modularStandardH1Winding a = ((0, -1) : ℤ × ℤ) from modularStandardH1Winding_generatorA,
    show modularStandardH1Winding b = ((-1, 0) : ℤ × ℤ) from modularStandardH1Winding_generatorB]
  ext <;> simp [originalToStandardCircleLabel]

/-- Every actual loop has its exact original fixed-I H1 coordinates recovered
from the actual standard coordinate winding. This is a proved comparison. -/
theorem modularTraceFixedSingularH1Equiv_loop_standardWinding
    {x : ModularTraceQuotient} (γ : Path x x) :
    modularTraceFixedSingularH1Equiv (singularLoopClass ModularTraceQuotient γ) =
      originalToStandardCircleLabel (modularStandardLoopWinding γ) := by
  have h := modularStandardH1Winding_fixedCoordinates
    (singularLoopClass ModularTraceQuotient γ)
  rw [modularStandardH1Winding_loop] at h
  have he := congrArg originalToStandardCircleLabel h
  rw [originalToStandardCircleLabel_involutive] at he
  exact he.symm

/-- The actual affine-circle loop has exactly the signed-interchanged standard
integer label in the original, fixed-I genuine singular H1 marking. -/
theorem modularAffineCircleLoop_fixedSingularCoordinates (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : NormalizedCircle) (hc : c ≠ 0) :
    modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient (modularAffineCircleLoop p q hpq c hc)) =
      (-p.2, -p.1) := by
  rw [modularTraceFixedSingularH1Equiv_loop_standardWinding,
    modularAffineCircleLoop_standardWinding]
  rfl

/-- Every primitive class in the original paper marking has a genuine actual
closed embedded affine-circle representative, with the exact original H1 label.
No simple-geodesic or canonical Farey-holonomy identification is implicit. -/
theorem modular_exists_embeddedAffineCircle_originalSingularClass (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    ∃ q : ℤ × ℤ, ∃ hpq : intDet (originalToStandardCircleLabel p) q = 1,
      IsClosedEmbedding (modularAffineCircle (originalToStandardCircleLabel p) q hpq
        standardCircleHalf standardCircleHalf_ne_zero) ∧
      modularTraceFixedSingularH1Equiv (singularLoopClass ModularTraceQuotient
        (modularAffineCircleLoop (originalToStandardCircleLabel p) q hpq
          standardCircleHalf standardCircleHalf_ne_zero)) = p := by
  obtain ⟨q, hpq⟩ := standardPrimitive_complement (originalToStandardCircleLabel p)
    (originalToStandardCircleLabel_isCoprime p hp)
  refine ⟨q, hpq, modularAffineCircle_isClosedEmbedding _ q hpq
    standardCircleHalf standardCircleHalf_ne_zero, ?_⟩
  rw [modularAffineCircleLoop_fixedSingularCoordinates]
  change originalToStandardCircleLabel (originalToStandardCircleLabel p) = p
  exact originalToStandardCircleLabel_involutive p

/-- An invariant existence statement with an actual circle embedding and its
actual positive once-around loop in the prescribed original primitive H1 class. -/
theorem modular_originalPrimitiveClass_has_closedEmbeddedRepresentative (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    ∃ (f : NormalizedCircle → ModularTraceQuotient) (hf : IsClosedEmbedding f),
      modularTraceFixedSingularH1Equiv
        (singularLoopClass ModularTraceQuotient
          (normalizedCircleStandardLoop.map hf.continuous)) = p := by
  obtain ⟨q, hpq, hemb, hclass⟩ :=
    modular_exists_embeddedAffineCircle_originalSingularClass p hp
  refine ⟨modularAffineCircle (originalToStandardCircleLabel p) q hpq
    standardCircleHalf standardCircleHalf_ne_zero, hemb, ?_⟩
  exact hclass

end Markov
