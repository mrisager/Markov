import Markov.ModularOriginalPrimitiveCircles

noncomputable section
open Topology
namespace Markov

/-- The actual two-circle torus map whose integer columns are p and q. -/
def standardTorusColumnMap (p q : ℤ × ℤ) (z : StandardTorus) : StandardTorus :=
  standardTorusIntegerCombination p q z.1 z.2

/-- The actual inverse dual-coordinate candidate, before imposing determinant one. -/
def standardTorusColumnDualMap (p q : ℤ × ℤ) (z : StandardTorus) : StandardTorus :=
  (standardTorusFirstDual q z, standardTorusSecondDual p z)

/-- The proved dual-coordinate identities give determinant scaling in one order. -/
theorem standardTorusColumnDualMap_columnMap (p q : ℤ × ℤ) (z : StandardTorus) :
    standardTorusColumnDualMap p q (standardTorusColumnMap p q z) = intDet p q • z := by
  apply Prod.ext
  · exact standardTorusFirstDual_integerCombination p q z.1 z.2
  · exact standardTorusSecondDual_integerCombination p q z.1 z.2

/-- The literal integer matrix identity gives determinant scaling in the other order. -/
theorem standardTorusColumnMap_dualMap (p q : ℤ × ℤ) (z : StandardTorus) :
    standardTorusColumnMap p q (standardTorusColumnDualMap p q z) = intDet p q • z := by
  apply Prod.ext
  · change p.1 • (q.2 • z.1 - q.1 • z.2) +
      q.1 • (p.1 • z.2 - p.2 • z.1) = intDet p q • z.1
    calc
      _ = (p.1 * q.2 - q.1 * p.2) • z.1 +
          (-p.1 * q.1 + q.1 * p.1) • z.2 := by
        simp only [smul_sub, smul_smul, sub_smul, add_smul, neg_mul, neg_smul]
        abel
      _ = intDet p q • z.1 := by
        have hdet : p.1 * q.2 - q.1 * p.2 = intDet p q := by unfold intDet; ring
        have hz : -p.1 * q.1 + q.1 * p.1 = 0 := by ring
        rw [hdet, hz, zero_smul, add_zero]
  · change p.2 • (q.2 • z.1 - q.1 • z.2) +
      q.2 • (p.1 • z.2 - p.2 • z.1) = intDet p q • z.2
    calc
      _ = (p.2 * q.2 - q.2 * p.2) • z.1 +
          (-p.2 * q.1 + q.2 * p.1) • z.2 := by
        simp only [smul_sub, smul_smul, sub_smul, add_smul, neg_mul, neg_smul]
        abel
      _ = intDet p q • z.2 := by
        have hz : p.2 * q.2 - q.2 * p.2 = 0 := by ring
        have hdet : -p.2 * q.1 + q.2 * p.1 = intDet p q := by unfold intDet; ring
        rw [hz, hdet, zero_smul, zero_add]

/-- A determinant-one integer column pair gives an actual standard-torus homeomorphism,
with the inverse given by the literal dual integer coordinates. -/
def standardUnimodularTorusHomeomorph (p q : ℤ × ℤ) (hpq : intDet p q = 1) :
    StandardTorus ≃ₜ StandardTorus where
  toFun := standardTorusColumnMap p q
  invFun := standardTorusColumnDualMap p q
  left_inv z := by rw [standardTorusColumnDualMap_columnMap, hpq, one_smul]
  right_inv z := by rw [standardTorusColumnMap_dualMap, hpq, one_smul]
  continuous_toFun := by unfold standardTorusColumnMap standardTorusIntegerCombination; fun_prop
  continuous_invFun := by
    unfold standardTorusColumnDualMap standardTorusFirstDual standardTorusSecondDual
    fun_prop

@[simp] theorem standardUnimodularTorusHomeomorph_zero (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) : standardUnimodularTorusHomeomorph p q hpq 0 = 0 := by
  change (p.1 • (0 : NormalizedCircle) + q.1 • 0, p.2 • (0 : NormalizedCircle) + q.2 • 0) = 0
  simp

/-- The actual determinant-one homeomorphism restricts to the actual complement of zero. -/
def standardUnimodularPuncturedTorusHomeomorph (p q : ℤ × ℤ) (hpq : intDet p q = 1) :
    StandardPuncturedTorus ≃ₜ StandardPuncturedTorus :=
  (standardUnimodularTorusHomeomorph p q hpq).subtype (fun z => by
    constructor
    · intro hz he
      apply hz
      apply (standardUnimodularTorusHomeomorph p q hpq).injective
      exact he.trans (standardUnimodularTorusHomeomorph_zero p q hpq).symm
    · intro hz he
      apply hz
      rw [he, standardUnimodularTorusHomeomorph_zero])

/-- Literal coordinate formula of the restricted actual homeomorphism. -/
theorem standardUnimodularPuncturedTorusHomeomorph_coe (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (z : StandardPuncturedTorus) :
    (standardUnimodularPuncturedTorusHomeomorph p q hpq z).val =
      standardTorusColumnMap p q z.val := rfl

/-- The corresponding actual surface homeomorphism is conjugated through the checked actual chart. -/
def modularUnimodularTorusHomeomorph (p q : ℤ × ℤ) (hpq : intDet p q = 1) :
    ModularTraceQuotient ≃ₜ ModularTraceQuotient :=
  (modularTraceQuotientPuncturedTorusHomeomorph.trans
    (standardUnimodularPuncturedTorusHomeomorph p q hpq)).trans
      modularTraceQuotientPuncturedTorusHomeomorph.symm

/-- The actual surface homeomorphism has exactly the prescribed standard-model action. -/
theorem modularUnimodularTorusHomeomorph_standard (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (z : ModularTraceQuotient) :
    modularTraceQuotientPuncturedTorusHomeomorph (modularUnimodularTorusHomeomorph p q hpq z) =
      standardUnimodularPuncturedTorusHomeomorph p q hpq
        (modularTraceQuotientPuncturedTorusHomeomorph z) :=
  Homeomorph.apply_symm_apply _ _

/-- The same integer columns acting on literal integer labels. -/
def integerColumnMap (p q u : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 * u.1 + q.1 * u.2, p.2 * u.1 + q.2 * u.2)

/-- Literal determinant multiplicativity for the integer-column map. -/
theorem integerColumnMap_intDet (p q u v : ℤ × ℤ) :
    intDet (integerColumnMap p q u) (integerColumnMap p q v) =
      intDet p q * intDet u v := by
  unfold integerColumnMap intDet
  ring

/-- The integer-column map sends unimodular pairs to unimodular pairs. -/
theorem integerColumnMap_unimodular (p q u v : ℤ × ℤ)
    (hpq : intDet p q = 1) (huv : intDet u v = 1) :
    intDet (integerColumnMap p q u) (integerColumnMap p q v) = 1 := by
  rw [integerColumnMap_intDet, hpq, huv, one_mul]

/-- The actual torus map sends every displayed affine two-circle combination
exactly to the combination of the transformed integer columns. -/
theorem standardTorusColumnMap_integerCombination (p q u v : ℤ × ℤ)
    (t c : NormalizedCircle) :
    standardTorusColumnMap p q (standardTorusIntegerCombination u v t c) =
      standardTorusIntegerCombination (integerColumnMap p q u) (integerColumnMap p q v) t c := by
  apply Prod.ext <;>
    simp only [standardTorusColumnMap, standardTorusIntegerCombination, integerColumnMap,
      smul_add, smul_smul, add_smul] <;> abel

/-- Exact affine-circle image formula in the actual punctured standard torus. -/
theorem standardUnimodularPuncturedTorusHomeomorph_affineCircle
    (p q u v : ℤ × ℤ) (hpq : intDet p q = 1) (huv : intDet u v = 1)
    (c : NormalizedCircle) (hc : c ≠ 0) (t : NormalizedCircle) :
    standardUnimodularPuncturedTorusHomeomorph p q hpq
      (standardPuncturedAffineCircle u v huv c hc t) =
    standardPuncturedAffineCircle (integerColumnMap p q u) (integerColumnMap p q v)
      (integerColumnMap_unimodular p q u v hpq huv) c hc t := by
  apply Subtype.ext
  exact standardTorusColumnMap_integerCombination p q u v t c

/-- Exact affine-circle image formula on the actual modular quotient surface. -/
theorem modularUnimodularTorusHomeomorph_affineCircle
    (p q u v : ℤ × ℤ) (hpq : intDet p q = 1) (huv : intDet u v = 1)
    (c : NormalizedCircle) (hc : c ≠ 0) (t : NormalizedCircle) :
    modularUnimodularTorusHomeomorph p q hpq (modularAffineCircle u v huv c hc t) =
    modularAffineCircle (integerColumnMap p q u) (integerColumnMap p q v)
      (integerColumnMap_unimodular p q u v hpq huv) c hc t := by
  apply modularTraceQuotientPuncturedTorusHomeomorph.injective
  rw [modularUnimodularTorusHomeomorph_standard]
  change standardUnimodularPuncturedTorusHomeomorph p q hpq
    (modularTraceQuotientPuncturedTorusHomeomorph
      (modularTraceQuotientPuncturedTorusHomeomorph.symm
        (standardPuncturedAffineCircle u v huv c hc t))) =
    modularTraceQuotientPuncturedTorusHomeomorph
      (modularTraceQuotientPuncturedTorusHomeomorph.symm _)
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  exact standardUnimodularPuncturedTorusHomeomorph_affineCircle p q u v hpq huv c hc t

/-- Actual singular classes depend only on the literal loop function, allowing
its equal endpoints to be displayed at different but equal basepoints. -/
theorem singularLoopClass_pointwise_eq {X : Type} [TopologicalSpace X]
    {x y : X} (γ : Path x x) (δ : Path y y) (h : ∀ t, γ t = δ t) :
    singularLoopClass X γ = singularLoopClass X δ := by
  have hxy : x = y := γ.source.symm.trans ((h 0).trans δ.source)
  cases hxy
  have he : γ = δ := Path.ext (funext h)
  rw [he]

/-- Exact original H1 coordinates of the actual mapped affine once-around loop. -/
theorem modularUnimodularTorusHomeomorph_affineCircleLoop_fixedH1
    (p q u v : ℤ × ℤ) (hpq : intDet p q = 1) (huv : intDet u v = 1)
    (c : NormalizedCircle) (hc : c ≠ 0) :
    modularTraceFixedSingularH1Equiv (singularLoopClass ModularTraceQuotient
      ((modularAffineCircleLoop u v huv c hc).map
        (modularUnimodularTorusHomeomorph p q hpq).continuous)) =
      originalToStandardCircleLabel (integerColumnMap p q u) := by
  have he := singularLoopClass_pointwise_eq
    ((modularAffineCircleLoop u v huv c hc).map
      (modularUnimodularTorusHomeomorph p q hpq).continuous)
    (modularAffineCircleLoop (integerColumnMap p q u) (integerColumnMap p q v)
      (integerColumnMap_unimodular p q u v hpq huv) c hc)
    (fun t => modularUnimodularTorusHomeomorph_affineCircle p q u v hpq huv c hc
      (normalizedCircleStandardLoop t))
  rw [he, modularAffineCircleLoop_fixedSingularCoordinates]
  rfl

/-- The resulting conjugated integer action in the original A/B coordinate convention. -/
def originalUnimodularCircleAction (p q r : ℤ × ℤ) : ℤ × ℤ :=
  originalToStandardCircleLabel (integerColumnMap p q (originalToStandardCircleLabel r))

/-- The original-coordinate matrix has columns (q.2,q.1) and (p.2,p.1). -/
theorem originalUnimodularCircleAction_formula (p q r : ℤ × ℤ) :
    originalUnimodularCircleAction p q r =
      (q.2 * r.1 + p.2 * r.2, q.1 * r.1 + p.1 * r.2) := by
  ext <;> simp [originalUnimodularCircleAction, originalToStandardCircleLabel, integerColumnMap]

/-- The actual homeomorphism realizes the prescribed original integer action
on every constructed affine representative of an original primitive class.
This is not an action on nonabelian words or a Farey free-homotopy theorem. -/
theorem modularUnimodularTorusHomeomorph_originalAffineCircleLoop_fixedH1
    (p q r v : ℤ × ℤ) (hpq : intDet p q = 1)
    (hrv : intDet (originalToStandardCircleLabel r) v = 1)
    (c : NormalizedCircle) (hc : c ≠ 0) :
    modularTraceFixedSingularH1Equiv (singularLoopClass ModularTraceQuotient
      ((modularAffineCircleLoop (originalToStandardCircleLabel r) v hrv c hc).map
        (modularUnimodularTorusHomeomorph p q hpq).continuous)) =
      originalUnimodularCircleAction p q r :=
  modularUnimodularTorusHomeomorph_affineCircleLoop_fixedH1
    p q (originalToStandardCircleLabel r) v hpq hrv c hc

end Markov
