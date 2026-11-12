import Markov.ModularOriginalPrimitiveCircles

noncomputable section
open Topology
namespace Markov

/-- The literal signed swap of the actual two-circle torus. It reverses the
ordered coordinate basis and is its own actual continuous inverse. -/
def standardSignedSwapTorusHomeomorph : StandardTorus ≃ₜ StandardTorus where
  toFun z := (-z.2, -z.1)
  invFun z := (-z.2, -z.1)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem standardSignedSwapTorusHomeomorph_apply (z : StandardTorus) :
    standardSignedSwapTorusHomeomorph z = (-z.2, -z.1) := rfl

@[simp] theorem standardSignedSwapTorusHomeomorph_zero :
    standardSignedSwapTorusHomeomorph 0 = 0 := by simp

theorem standardSignedSwapTorusHomeomorph_involutive :
    Function.Involutive standardSignedSwapTorusHomeomorph := by
  intro z
  ext <;> simp

/-- The actual signed swap restricts to the actual complement of the zero puncture. -/
def standardSignedSwapPuncturedTorusHomeomorph :
    StandardPuncturedTorus ≃ₜ StandardPuncturedTorus :=
  standardSignedSwapTorusHomeomorph.subtype (fun z => by
    constructor
    · intro hz he
      apply hz
      apply standardSignedSwapTorusHomeomorph.injective
      exact he.trans standardSignedSwapTorusHomeomorph_zero.symm
    · intro hz he
      apply hz
      rw [he, standardSignedSwapTorusHomeomorph_zero])

/-- Literal coordinate action on the actual punctured standard torus. -/
theorem standardSignedSwapPuncturedTorusHomeomorph_coe (z : StandardPuncturedTorus) :
    (standardSignedSwapPuncturedTorusHomeomorph z).val = (-z.val.2, -z.val.1) := rfl

theorem standardSignedSwapPuncturedTorusHomeomorph_involutive :
    Function.Involutive standardSignedSwapPuncturedTorusHomeomorph := by
  intro z
  apply Subtype.ext
  change (-(-z.val.1), -(-z.val.2)) = z.val
  simp

/-- Conjugation through the actual checked chart gives a genuine surface homeomorphism. -/
def modularSignedSwapTorusHomeomorph : ModularTraceQuotient ≃ₜ ModularTraceQuotient :=
  (modularTraceQuotientPuncturedTorusHomeomorph.trans
    standardSignedSwapPuncturedTorusHomeomorph).trans
      modularTraceQuotientPuncturedTorusHomeomorph.symm

/-- The actual modular signed swap has exactly the literal standard-model action. -/
theorem modularSignedSwapTorusHomeomorph_standard (z : ModularTraceQuotient) :
    modularTraceQuotientPuncturedTorusHomeomorph (modularSignedSwapTorusHomeomorph z) =
      standardSignedSwapPuncturedTorusHomeomorph
        (modularTraceQuotientPuncturedTorusHomeomorph z) :=
  Homeomorph.apply_symm_apply _ _

theorem modularSignedSwapTorusHomeomorph_involutive :
    Function.Involutive modularSignedSwapTorusHomeomorph := by
  intro z
  apply modularTraceQuotientPuncturedTorusHomeomorph.injective
  rw [modularSignedSwapTorusHomeomorph_standard, modularSignedSwapTorusHomeomorph_standard,
    standardSignedSwapPuncturedTorusHomeomorph_involutive]

/-- The positive ordered standard columns become the literal original A/B
standard-model directions, with their required determinant minus one. -/
theorem signedSwap_originalGeneratorColumns :
    originalToStandardCircleLabel ((1, 0) : ℤ × ℤ) = (0, -1) ∧
    originalToStandardCircleLabel ((0, 1) : ℤ × ℤ) = (-1, 0) ∧
    intDet (originalToStandardCircleLabel ((1, 0) : ℤ × ℤ))
      (originalToStandardCircleLabel ((0, 1) : ℤ × ℤ)) = -1 := by
  norm_num [originalToStandardCircleLabel, intDet]

/-- The signed interchange reverses the literal integer determinant. -/
theorem originalToStandardCircleLabel_intDet (p q : ℤ × ℤ) :
    intDet (originalToStandardCircleLabel p) (originalToStandardCircleLabel q) =
      -intDet p q := by
  unfold originalToStandardCircleLabel intDet
  ring

/-- Reversing the transformed partner restores determinant one. -/
theorem signedSwapAffinePartner_intDet (p q : ℤ × ℤ) :
    intDet (originalToStandardCircleLabel p) (-originalToStandardCircleLabel q) = intDet p q := by
  unfold originalToStandardCircleLabel intDet
  simp only [Prod.fst_neg, Prod.snd_neg]
  ring

/-- The literal signed swap acts on each of the two integer columns by Jp=(-p.2,-p.1). -/
theorem standardSignedSwapTorusHomeomorph_integerCombination (p q : ℤ × ℤ)
    (t c : NormalizedCircle) :
    standardSignedSwapTorusHomeomorph (standardTorusIntegerCombination p q t c) =
      standardTorusIntegerCombination (originalToStandardCircleLabel p)
        (originalToStandardCircleLabel q) t c := by
  ext <;> simp [standardTorusIntegerCombination, originalToStandardCircleLabel, neg_smul, add_comm]

/-- Exact transformed affine-circle parametrization; the negative partner and
negative transverse offset retain the determinant-one construction. -/
theorem standardSignedSwapPuncturedTorusHomeomorph_affineCircle
    (p q : ℤ × ℤ) (hpq : intDet p q = 1)
    (c : NormalizedCircle) (hc : c ≠ 0) (t : NormalizedCircle) :
    standardSignedSwapPuncturedTorusHomeomorph (standardPuncturedAffineCircle p q hpq c hc t) =
      standardPuncturedAffineCircle (originalToStandardCircleLabel p)
        (-originalToStandardCircleLabel q)
        ((signedSwapAffinePartner_intDet p q).trans hpq)
        (-c) (neg_ne_zero.mpr hc) t := by
  apply Subtype.ext
  ext <;> simp [standardSignedSwapPuncturedTorusHomeomorph_coe, standardPuncturedAffineCircle,
    standardTorusIntegerCombination, originalToStandardCircleLabel, neg_smul, smul_neg, add_comm]

/-- Exact affine-circle image under the actual modular-surface signed swap. -/
theorem modularSignedSwapTorusHomeomorph_affineCircle
    (p q : ℤ × ℤ) (hpq : intDet p q = 1)
    (c : NormalizedCircle) (hc : c ≠ 0) (t : NormalizedCircle) :
    modularSignedSwapTorusHomeomorph (modularAffineCircle p q hpq c hc t) =
      modularAffineCircle (originalToStandardCircleLabel p)
        (-originalToStandardCircleLabel q)
        ((signedSwapAffinePartner_intDet p q).trans hpq)
        (-c) (neg_ne_zero.mpr hc) t := by
  apply modularTraceQuotientPuncturedTorusHomeomorph.injective
  rw [modularSignedSwapTorusHomeomorph_standard]
  change standardSignedSwapPuncturedTorusHomeomorph
    (modularTraceQuotientPuncturedTorusHomeomorph
      (modularTraceQuotientPuncturedTorusHomeomorph.symm
        (standardPuncturedAffineCircle p q hpq c hc t))) =
    modularTraceQuotientPuncturedTorusHomeomorph
      (modularTraceQuotientPuncturedTorusHomeomorph.symm _)
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  exact standardSignedSwapPuncturedTorusHomeomorph_affineCircle p q hpq c hc t

private theorem signedSwapLoopClass_pointwise {X : Type} [TopologicalSpace X]
    {x y : X} (γ : Path x x) (δ : Path y y) (h : ∀ t, γ t = δ t) :
    singularLoopClass X γ = singularLoopClass X δ := by
  have hxy : x = y := γ.source.symm.trans ((h 0).trans δ.source)
  cases hxy
  have he : γ = δ := Path.ext (funext h)
  rw [he]

/-- The mapped standard-labelled affine loop has original fixed-I H1 label p,
because the actual signed swap supplies the required orientation reversal. -/
theorem modularSignedSwapTorusHomeomorph_affineCircleLoop_fixedH1
    (p q : ℤ × ℤ) (hpq : intDet p q = 1) (c : NormalizedCircle) (hc : c ≠ 0) :
    modularTraceFixedSingularH1Equiv (singularLoopClass ModularTraceQuotient
      ((modularAffineCircleLoop p q hpq c hc).map modularSignedSwapTorusHomeomorph.continuous)) = p := by
  have he := signedSwapLoopClass_pointwise
    ((modularAffineCircleLoop p q hpq c hc).map modularSignedSwapTorusHomeomorph.continuous)
    (modularAffineCircleLoop (originalToStandardCircleLabel p) (-originalToStandardCircleLabel q)
      ((signedSwapAffinePartner_intDet p q).trans hpq) (-c) (neg_ne_zero.mpr hc))
    (fun t => modularSignedSwapTorusHomeomorph_affineCircle p q hpq c hc (normalizedCircleStandardLoop t))
  rw [he, modularAffineCircleLoop_fixedSingularCoordinates]
  change originalToStandardCircleLabel (originalToStandardCircleLabel p) = p
  exact originalToStandardCircleLabel_involutive p

/-- On constructed representatives with original class r, the actual signed
swap gives the original class Jr. No nonabelian word action is inferred. -/
theorem modularSignedSwapTorusHomeomorph_originalAffineCircleLoop_fixedH1
    (r q : ℤ × ℤ) (hrq : intDet (originalToStandardCircleLabel r) q = 1)
    (c : NormalizedCircle) (hc : c ≠ 0) :
    modularTraceFixedSingularH1Equiv (singularLoopClass ModularTraceQuotient
      ((modularAffineCircleLoop (originalToStandardCircleLabel r) q hrq c hc).map
        modularSignedSwapTorusHomeomorph.continuous)) = originalToStandardCircleLabel r :=
  modularSignedSwapTorusHomeomorph_affineCircleLoop_fixedH1
    (originalToStandardCircleLabel r) q hrq c hc

end Markov
