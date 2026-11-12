import Markov.StandardTorusSquare
import Markov.FareyHolonomy

noncomputable section
open Set Topology
namespace Markov

/-- Integer linear combination in the literal two-circle torus. -/
def standardTorusIntegerCombination (p q : ℤ × ℤ)
    (t s : AddCircle (1 : ℝ)) : StandardTorus :=
  (p.1 • t + q.1 • s, p.2 • t + q.2 • s)

/-- The first dual coordinate for the two indicated integer columns. -/
def standardTorusFirstDual (q : ℤ × ℤ) (z : StandardTorus) : AddCircle (1 : ℝ) :=
  q.2 • z.1 - q.1 • z.2

/-- The second dual coordinate for the two indicated integer columns. -/
def standardTorusSecondDual (p : ℤ × ℤ) (z : StandardTorus) : AddCircle (1 : ℝ) :=
  p.1 • z.2 - p.2 • z.1

/-- The determinant gives the exact first coordinate of the inverse integer map. -/
theorem standardTorusFirstDual_integerCombination (p q : ℤ × ℤ)
    (t s : AddCircle (1 : ℝ)) :
    standardTorusFirstDual q (standardTorusIntegerCombination p q t s) =
      intDet p q • t := by
  unfold standardTorusFirstDual standardTorusIntegerCombination
  change q.2 • (p.1 • t + q.1 • s) - q.1 • (p.2 • t + q.2 • s) = _
  calc
    _ = (q.2 * p.1 - q.1 * p.2) • t + (q.2 * q.1 - q.1 * q.2) • s := by
      simp only [smul_add, smul_smul, sub_smul]
      abel
    _ = intDet p q • t := by
      have ht : q.2 * p.1 - q.1 * p.2 = intDet p q := by unfold intDet; ring
      have hs : q.2 * q.1 - q.1 * q.2 = 0 := by ring
      rw [ht, hs, zero_smul, add_zero]

/-- The determinant gives the exact second coordinate of the inverse integer map. -/
theorem standardTorusSecondDual_integerCombination (p q : ℤ × ℤ)
    (t s : AddCircle (1 : ℝ)) :
    standardTorusSecondDual p (standardTorusIntegerCombination p q t s) =
      intDet p q • s := by
  unfold standardTorusSecondDual standardTorusIntegerCombination
  change p.1 • (p.2 • t + q.2 • s) - p.2 • (p.1 • t + q.1 • s) = _
  calc
    _ = (p.1 * p.2 - p.2 * p.1) • t + (p.1 * q.2 - p.2 * q.1) • s := by
      simp only [smul_add, smul_smul, sub_smul]
      abel
    _ = intDet p q • s := by
      have ht : p.1 * p.2 - p.2 * p.1 = 0 := by ring
      rw [ht, zero_smul, zero_add]
      rfl

/-- Every primitive signed integer pair has an orientation-one complementary pair. -/
theorem standardPrimitive_complement (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    ∃ q : ℤ × ℤ, intDet p q = 1 := by
  obtain ⟨a, b, h⟩ := hp
  refine ⟨(-b, a), ?_⟩
  dsimp [intDet]
  linear_combination h

/-- A nonzero transverse circle coordinate keeps the whole affine circle off the puncture. -/
theorem standardTorusIntegerCombination_ne_zero (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0)
    (t : AddCircle (1 : ℝ)) : standardTorusIntegerCombination p q t c ≠ 0 := by
  intro h
  have hs := standardTorusSecondDual_integerCombination p q t c
  rw [hpq, one_smul, h] at hs
  exact hc (by simpa [standardTorusSecondDual] using hs.symm)

/-- The actual affine circle, as a map to the actual standard punctured torus. -/
def standardPuncturedAffineCircle (p q : ℤ × ℤ) (hpq : intDet p q = 1)
    (c : AddCircle (1 : ℝ)) (hc : c ≠ 0)
    (t : AddCircle (1 : ℝ)) : StandardPuncturedTorus :=
  ⟨standardTorusIntegerCombination p q t c,
    standardTorusIntegerCombination_ne_zero p q hpq c hc t⟩

/-- The first dual coordinate is a literal continuous left inverse on the affine circle. -/
theorem standardPuncturedAffineCircle_firstDual (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0)
    (t : AddCircle (1 : ℝ)) :
    standardTorusFirstDual q (standardPuncturedAffineCircle p q hpq c hc t).1 = t := by
  exact (standardTorusFirstDual_integerCombination p q t c).trans (by rw [hpq, one_smul])

theorem continuous_standardTorusFirstDual (q : ℤ × ℤ) :
    Continuous (standardTorusFirstDual q) := by
  unfold standardTorusFirstDual
  fun_prop

theorem continuous_standardPuncturedAffineCircle (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) :
    Continuous (standardPuncturedAffineCircle p q hpq c hc) := by
  unfold standardPuncturedAffineCircle standardTorusIntegerCombination
  fun_prop

theorem standardPuncturedAffineCircle_injective (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) :
    Function.Injective (standardPuncturedAffineCircle p q hpq c hc) := by
  intro t s h
  have hd := congrArg (fun z : StandardPuncturedTorus => standardTorusFirstDual q z.1) h
  simpa only [standardPuncturedAffineCircle_firstDual] using hd

/-- Compactness upgrades the literal continuous injective circle to a closed embedding. -/
theorem standardPuncturedAffineCircle_isClosedEmbedding (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) :
    IsClosedEmbedding (standardPuncturedAffineCircle p q hpq c hc) :=
  (continuous_standardPuncturedAffineCircle p q hpq c hc).isClosedEmbedding
    (standardPuncturedAffineCircle_injective p q hpq c hc)

/-- The second dual coordinate records the chosen transverse offset exactly. -/
theorem standardPuncturedAffineCircle_secondDual (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0)
    (t : AddCircle (1 : ℝ)) :
    standardTorusSecondDual p (standardPuncturedAffineCircle p q hpq c hc t).1 = c := by
  exact (standardTorusSecondDual_integerCombination p q t c).trans (by rw [hpq, one_smul])

/-- The first integer dual coordinate on the entire punctured standard torus. -/
def standardPuncturedTorusCircleRetraction (q : ℤ × ℤ)
    (z : StandardPuncturedTorus) : AddCircle (1 : ℝ) :=
  standardTorusFirstDual q z.1

theorem continuous_standardPuncturedTorusCircleRetraction (q : ℤ × ℤ) :
    Continuous (standardPuncturedTorusCircleRetraction q) :=
  (continuous_standardTorusFirstDual q).comp continuous_subtype_val

/-- A continuous left inverse exists on the entire punctured torus. This
is the explicit retraction identity; no homotopy-class assertion is implicit. -/
theorem standardPuncturedAffineCircle_leftInverse (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) :
    Function.LeftInverse (standardPuncturedTorusCircleRetraction q)
      (standardPuncturedAffineCircle p q hpq c hc) :=
  standardPuncturedAffineCircle_firstDual p q hpq c hc

/-- Function-level composition form of the literal retraction identity. -/
theorem standardPuncturedAffineCircle_retraction_comp (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : AddCircle (1 : ℝ)) (hc : c ≠ 0) :
    standardPuncturedTorusCircleRetraction q ∘
      standardPuncturedAffineCircle p q hpq c hc = id := by
  funext t
  exact standardPuncturedAffineCircle_leftInverse p q hpq c hc t

/-- The literal half-period class used for a concrete puncture-avoiding offset. -/
def standardCircleHalf : AddCircle (1 : ℝ) := ((1 / 2 : ℝ) : AddCircle (1 : ℝ))

theorem standardCircleHalf_ne_zero : standardCircleHalf ≠ 0 := by
  unfold standardCircleHalf
  intro h
  have hzero : (1 / 2 : ℝ) = 0 :=
    (AddCircle.coe_eq_zero_iff_of_mem_Ico
      (show (1 / 2 : ℝ) ∈ Ico 0 1 by norm_num)).mp h
  norm_num at hzero

/-- Every primitive signed integer pair has an actual embedded affine circle
in the standard torus with the origin removed. This does not identify its
original paper marking or its singular-homology class. -/
theorem standardPrimitive_exists_embeddedAffineCircle (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    ∃ q : ℤ × ℤ, ∃ hpq : intDet p q = 1,
      IsClosedEmbedding
        (standardPuncturedAffineCircle p q hpq standardCircleHalf standardCircleHalf_ne_zero) := by
  obtain ⟨q, hpq⟩ := standardPrimitive_complement p hp
  exact ⟨q, hpq, standardPuncturedAffineCircle_isClosedEmbedding p q hpq
    standardCircleHalf standardCircleHalf_ne_zero⟩

end Markov
