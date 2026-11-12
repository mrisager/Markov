import Markov.DiskArcChordHomotopy

/-! Pure actual complex quarter turns for RAW-square corner transport.
These are explicit complex linear maps. No Q rotation, quotient isometry,
boundary ordering, normal diagram, or classification field is assumed. -/

noncomputable section
namespace Markov

/-- The literal quarter turn bringing side k to TOP, in side order
TOP,RIGHT,BOTTOM,LEFT. -/
def rawSquareQuarterTurn (k : Fin 4) (z : ℂ) : ℂ := ![z, Complex.I*z, -z, -Complex.I*z] k

/-- Each actual complex quarter turn is injective. -/
theorem rawSquareQuarterTurn_injective (k : Fin 4) : Function.Injective (rawSquareQuarterTurn k) := by
  intro z w h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  apply Complex.ext <;> fin_cases k <;>
    simp [rawSquareQuarterTurn,Complex.mul_re,Complex.mul_im] at hr hi <;> linarith

/-- Literal complex subtraction commutes with each actual quarter turn. -/
theorem rawSquareQuarterTurn_sub (k : Fin 4) (z w : ℂ) :
    rawSquareQuarterTurn k (z-w)=rawSquareQuarterTurn k z-rawSquareQuarterTurn k w := by
  fin_cases k <;> dsimp [rawSquareQuarterTurn] <;> ring

/-- Endpoint chords commute exactly with the actual complex quarter turn. -/
theorem rawSquareQuarterTurn_diskArcChord (k : Fin 4) (f : unitInterval → ℂ)
    (t : unitInterval) :
    diskArcChord (rawSquareQuarterTurn k ∘ f) t=rawSquareQuarterTurn k (diskArcChord f t) := by
  fin_cases k <;> dsimp [rawSquareQuarterTurn,diskArcChord,Function.comp_apply] <;> ring

/-- The actual oriented two-dimensional determinant is preserved. -/
theorem rawSquareQuarterTurn_det (k : Fin 4) (z w : ℂ) :
    (rawSquareQuarterTurn k z).re*(rawSquareQuarterTurn k w).im-
        (rawSquareQuarterTurn k z).im*(rawSquareQuarterTurn k w).re =
      z.re*w.im-z.im*w.re := by
  fin_cases k <;>
    simp [rawSquareQuarterTurn,Complex.mul_re,Complex.mul_im] <;> ring

/-- In particular, the determinant of actual endpoint differences is preserved. -/
theorem rawSquareQuarterTurn_det_sub (k : Fin 4) (a b c d : ℂ) :
    (rawSquareQuarterTurn k a-rawSquareQuarterTurn k b).re*
        (rawSquareQuarterTurn k c-rawSquareQuarterTurn k d).im-
      (rawSquareQuarterTurn k a-rawSquareQuarterTurn k b).im*
        (rawSquareQuarterTurn k c-rawSquareQuarterTurn k d).re =
      (a-b).re*(c-d).im-(a-b).im*(c-d).re := by
  rw [← rawSquareQuarterTurn_sub k a b,← rawSquareQuarterTurn_sub k c d]
  exact rawSquareQuarterTurn_det k (a-b) (c-d)

/-- Actual strict open-square coordinate bounds are preserved by each literal
complex quarter turn; this transports constructed chord bounds. -/
theorem rawSquareQuarterTurn_strict_coordinates (k : Fin 4) (z : ℂ)
    (hz : (-1<z.re ∧ z.re<1) ∧ (-1<z.im ∧ z.im<1)) :
    (-1<(rawSquareQuarterTurn k z).re ∧ (rawSquareQuarterTurn k z).re<1) ∧
      (-1<(rawSquareQuarterTurn k z).im ∧ (rawSquareQuarterTurn k z).im<1) := by
  fin_cases k <;>
    simp [rawSquareQuarterTurn,Complex.mul_re,Complex.mul_im] <;>
    constructor <;> constructor <;> linarith [hz.1.1,hz.1.2,hz.2.1,hz.2.2]

/-- Actual CLOSED-square coordinate bounds are also preserved, so boundary
endpoint data transports by the same literal complex maps. -/
theorem rawSquareQuarterTurn_closed_coordinates (k : Fin 4) (z : ℂ)
    (hz : (-1≤z.re ∧ z.re≤1) ∧ (-1≤z.im ∧ z.im≤1)) :
    (-1≤(rawSquareQuarterTurn k z).re ∧ (rawSquareQuarterTurn k z).re≤1) ∧
      (-1≤(rawSquareQuarterTurn k z).im ∧ (rawSquareQuarterTurn k z).im≤1) := by
  fin_cases k <;>
    simp [rawSquareQuarterTurn,Complex.mul_re,Complex.mul_im] <;>
    constructor <;> constructor <;> linarith [hz.1.1,hz.1.2,hz.2.1,hz.2.2]

end Markov
