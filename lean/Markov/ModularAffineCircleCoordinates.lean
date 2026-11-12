import Markov.PaperGeneratorSquareWinding
import Markov.EmbeddedCircleSingularH1

noncomputable section
open Topology
namespace Markov

/-- Concrete translated coordinate winding of the actual mapped quotient loop. -/
def modularStandardLoopWinding {x : ModularTraceQuotient} (γ : Path x x) : ℤ × ℤ :=
  standardTorusLoopWinding
    (γ.map modularTraceQuotientPuncturedTorusHomeomorph.continuous)

/-- The first coordinate of the mapped affine-circle loop is the integer segment p.1. -/
theorem modularAffineCircleLoop_firstCoordinate (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : NormalizedCircle) (hc : c ≠ 0) :
    standardTorusFirstCoordinateLoop
      ((modularAffineCircleLoop p q hpq c hc).map
        modularTraceQuotientPuncturedTorusHomeomorph.continuous) =
      normalizedCircleIntegerLoop p.1 := by
  ext t
  change (modularTraceQuotientPuncturedTorusHomeomorph
      (modularTraceQuotientPuncturedTorusHomeomorph.symm
        (standardPuncturedAffineCircle p q hpq c hc (normalizedCircleStandardLoop t)))).val.1 -
    (modularTraceQuotientPuncturedTorusHomeomorph
      (modularTraceQuotientPuncturedTorusHomeomorph.symm
        (standardPuncturedAffineCircle p q hpq c hc 0))).val.1 = _
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  change p.1 • normalizedCircleStandardLoop t + q.1 • c - (p.1 • (0 : NormalizedCircle) + q.1 • c) = _
  rw [smul_zero, zero_add, add_sub_cancel_right, normalizedCircleStandardLoop_apply,
    normalizedCircleIntegerLoop_apply, ← AddCircle.coe_zsmul]
  congr 1
  simp only [zsmul_eq_mul, mul_comm]

/-- The second coordinate of the mapped affine-circle loop is the integer segment p.2. -/
theorem modularAffineCircleLoop_secondCoordinate (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : NormalizedCircle) (hc : c ≠ 0) :
    standardTorusSecondCoordinateLoop
      ((modularAffineCircleLoop p q hpq c hc).map
        modularTraceQuotientPuncturedTorusHomeomorph.continuous) =
      normalizedCircleIntegerLoop p.2 := by
  ext t
  change (modularTraceQuotientPuncturedTorusHomeomorph
      (modularTraceQuotientPuncturedTorusHomeomorph.symm
        (standardPuncturedAffineCircle p q hpq c hc (normalizedCircleStandardLoop t)))).val.2 -
    (modularTraceQuotientPuncturedTorusHomeomorph
      (modularTraceQuotientPuncturedTorusHomeomorph.symm
        (standardPuncturedAffineCircle p q hpq c hc 0))).val.2 = _
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  change p.2 • normalizedCircleStandardLoop t + q.2 • c - (p.2 • (0 : NormalizedCircle) + q.2 • c) = _
  rw [smul_zero, zero_add, add_sub_cancel_right, normalizedCircleStandardLoop_apply,
    normalizedCircleIntegerLoop_apply, ← AddCircle.coe_zsmul]
  congr 1
  simp only [zsmul_eq_mul, mul_comm]

/-- Exact standard-model winding of the actual once-around affine loop. -/
theorem modularAffineCircleLoop_standardWinding (p q : ℤ × ℤ)
    (hpq : intDet p q = 1) (c : NormalizedCircle) (hc : c ≠ 0) :
    modularStandardLoopWinding (modularAffineCircleLoop p q hpq c hc) = p := by
  unfold modularStandardLoopWinding standardTorusLoopWinding
  rw [modularAffineCircleLoop_firstCoordinate, modularAffineCircleLoop_secondCoordinate,
    normalizedCircleWinding_integerLoop, normalizedCircleWinding_integerLoop]

/-- The basis conversion suggested by the proved original A/B generator loops. -/
def originalToStandardCircleLabel (p : ℤ × ℤ) : ℤ × ℤ := (-p.2, -p.1)

theorem originalToStandardCircleLabel_involutive :
    Function.Involutive originalToStandardCircleLabel := by
  intro p
  simp [originalToStandardCircleLabel]

/-- The signed interchange preserves primitive integer labels. -/
theorem originalToStandardCircleLabel_isCoprime (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    IsCoprime (originalToStandardCircleLabel p).1 (originalToStandardCircleLabel p).2 := by
  obtain ⟨a, b, h⟩ := hp
  refine ⟨-b, -a, ?_⟩
  dsimp [originalToStandardCircleLabel]
  linear_combination h

end Markov
