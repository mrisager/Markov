import Markov.StandardPrimitiveCircles
import Markov.ModularEmbeddedCircles

/-! Explicit determinant-one affine circles on the actual punctured torus
intersect at exactly one point. This is an actual point-set intersection result;
no surgery, free-homotopy, holonomy or geodesic classification is asserted. -/

noncomputable section
open Set Topology
namespace Markov

/-- Keeping the first dual coordinate nonzero also avoids the actual puncture. -/
theorem standardTorusSecondAffineCircle_ne_zero (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0)
    (s : AddCircle (1 : ℝ)) : standardTorusIntegerCombination p q c s ≠ 0 := by
  intro h
  have hd := standardTorusFirstDual_integerCombination p q c s
  rw [hpq, one_smul, h] at hd
  exact hc (by simpa [standardTorusFirstDual] using hd.symm)

/-- The complementary actual affine circle, with direction q and transverse
coordinate c along p, retaining the original determinant-one column order. -/
def standardPuncturedSecondAffineCircle (p q : ℤ × ℤ) (hpq : intDet p q = 1)
    (c : AddCircle (1 : ℝ)) (hc : c ≠ 0)
    (s : AddCircle (1 : ℝ)) : StandardPuncturedTorus :=
  ⟨standardTorusIntegerCombination p q c s,
    standardTorusSecondAffineCircle_ne_zero p q hpq c hc s⟩

/-- The first dual coordinate of the complementary circle is its fixed offset. -/
theorem standardPuncturedSecondAffineCircle_firstDual (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0)
    (s : AddCircle (1 : ℝ)) :
    standardTorusFirstDual q (standardPuncturedSecondAffineCircle p q hpq c hc s).1 = c := by
  exact (standardTorusFirstDual_integerCombination p q c s).trans (by rw [hpq, one_smul])

/-- The second dual coordinate is a literal continuous left inverse. -/
theorem standardPuncturedSecondAffineCircle_secondDual (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0)
    (s : AddCircle (1 : ℝ)) :
    standardTorusSecondDual p (standardPuncturedSecondAffineCircle p q hpq c hc s).1 = s := by
  exact (standardTorusSecondDual_integerCombination p q c s).trans (by rw [hpq, one_smul])

theorem continuous_standardTorusSecondDual (p : ℤ × ℤ) :
    Continuous (standardTorusSecondDual p) := by
  unfold standardTorusSecondDual
  fun_prop

theorem continuous_standardPuncturedSecondAffineCircle (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) :
    Continuous (standardPuncturedSecondAffineCircle p q hpq c hc) := by
  unfold standardPuncturedSecondAffineCircle standardTorusIntegerCombination
  fun_prop

theorem standardPuncturedSecondAffineCircle_injective (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) :
    Function.Injective (standardPuncturedSecondAffineCircle p q hpq c hc) := by
  intro s t h
  have hd := congrArg (fun z : StandardPuncturedTorus => standardTorusSecondDual p z.1) h
  simpa only [standardPuncturedSecondAffineCircle_secondDual] using hd

/-- The complementary actual affine circle is a genuine closed embedding. -/
theorem standardPuncturedSecondAffineCircle_isClosedEmbedding (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) :
    IsClosedEmbedding (standardPuncturedSecondAffineCircle p q hpq c hc) :=
  (continuous_standardPuncturedSecondAffineCircle p q hpq c hc).isClosedEmbedding
    (standardPuncturedSecondAffineCircle_injective p q hpq c hc)

/-- Exact parameter-level intersection: both parameters must equal the offset. -/
theorem standardPuncturedAffineCircle_eq_second_iff (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0)
    (t s : AddCircle (1 : ℝ)) :
    standardPuncturedAffineCircle p q hpq c hc t =
      standardPuncturedSecondAffineCircle p q hpq c hc s ↔ t = c ∧ s = c := by
  constructor
  · intro h
    have hfirst := congrArg (fun z : StandardPuncturedTorus => standardTorusFirstDual q z.1) h
    have hsecond := congrArg (fun z : StandardPuncturedTorus => standardTorusSecondDual p z.1) h
    dsimp only at hfirst hsecond
    rw [standardPuncturedAffineCircle_firstDual,
      standardPuncturedSecondAffineCircle_firstDual] at hfirst
    rw [standardPuncturedAffineCircle_secondDual,
      standardPuncturedSecondAffineCircle_secondDual] at hsecond
    exact ⟨hfirst, hsecond.symm⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The actual embedded-circle images have exactly one common point. -/
theorem standardPuncturedAffineCircle_range_inter_second (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) :
    range (standardPuncturedAffineCircle p q hpq c hc) ∩
      range (standardPuncturedSecondAffineCircle p q hpq c hc) =
        {standardPuncturedAffineCircle p q hpq c hc c} := by
  ext z
  constructor
  · rintro ⟨⟨t, rfl⟩, ⟨s, hs⟩⟩
    have ht := ((standardPuncturedAffineCircle_eq_second_iff p q hpq c hc t s).mp hs.symm).1
    subst t
    rfl
  · intro hz
    have hz' : z = standardPuncturedAffineCircle p q hpq c hc c := hz
    subst z
    exact ⟨⟨c, rfl⟩, ⟨c, rfl⟩⟩

/-- The actual modular surface's complementary affine circle, via the proved homeomorphism. -/
def modularSecondAffineCircle (p q : ℤ × ℤ) (hpq : intDet p q = 1)
    (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) : AddCircle (1 : ℝ) → ModularTraceQuotient :=
  modularTraceQuotientPuncturedTorusHomeomorph.symm ∘
    standardPuncturedSecondAffineCircle p q hpq c hc

theorem continuous_modularSecondAffineCircle (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) :
    Continuous (modularSecondAffineCircle p q hpq c hc) :=
  modularTraceQuotientPuncturedTorusHomeomorph.symm.continuous.comp
    (continuous_standardPuncturedSecondAffineCircle p q hpq c hc)

theorem modularSecondAffineCircle_isClosedEmbedding (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) :
    IsClosedEmbedding (modularSecondAffineCircle p q hpq c hc) :=
  modularTraceQuotientPuncturedTorusHomeomorph.symm.isClosedEmbedding.comp
    (standardPuncturedSecondAffineCircle_isClosedEmbedding p q hpq c hc)

/-- Exact parameter-level once intersection on the actual modular quotient. -/
theorem modularAffineCircle_eq_second_iff (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0)
    (t s : AddCircle (1 : ℝ)) :
    modularAffineCircle p q hpq c hc t = modularSecondAffineCircle p q hpq c hc s ↔
      t = c ∧ s = c := by
  change modularTraceQuotientPuncturedTorusHomeomorph.symm
    (standardPuncturedAffineCircle p q hpq c hc t) =
      modularTraceQuotientPuncturedTorusHomeomorph.symm
        (standardPuncturedSecondAffineCircle p q hpq c hc s) ↔ _
  rw [modularTraceQuotientPuncturedTorusHomeomorph.symm.injective.eq_iff]
  exact standardPuncturedAffineCircle_eq_second_iff p q hpq c hc t s

/-- The actual modular embedded-circle images meet at exactly the common affine point. -/
theorem modularAffineCircle_range_inter_second (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) :
    range (modularAffineCircle p q hpq c hc) ∩
      range (modularSecondAffineCircle p q hpq c hc) =
        {modularAffineCircle p q hpq c hc c} := by
  ext z
  constructor
  · rintro ⟨⟨t, rfl⟩, ⟨s, hs⟩⟩
    have ht := ((modularAffineCircle_eq_second_iff p q hpq c hc t s).mp hs.symm).1
    subst t
    rfl
  · intro hz
    have hz' : z = modularAffineCircle p q hpq c hc c := hz
    subst z
    exact ⟨⟨c, rfl⟩, ⟨c, rfl⟩⟩

end Markov
