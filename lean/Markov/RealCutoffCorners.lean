import Markov.CutoffArcs
import Mathlib.Algebra.Order.Floor.Ring

/-! The actual primitive corner cutoff at a real height. Integral heights
identify this set exactly with the existing finite natural-height cutoff. -/

noncomputable section

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Primitive integral directions of real height at most `H`, normalized
to points of the actual norm unit boundary. -/
def realCutoffCorners (B : Module.Basis (Fin 2) ℝ E) (H : ℝ) : Set E :=
  {x | ∃ p : ℤ × ℤ, IsCoprime p.1 p.2 ∧ intHeight p ≤ H ∧
    x = NormedSpace.normalize (intVector B p)}

theorem mem_realCutoffCorners (B : Module.Basis (Fin 2) ℝ E) (H : ℝ) (x : E) :
    x ∈ realCutoffCorners B H ↔
      ∃ p : ℤ × ℤ, IsCoprime p.1 p.2 ∧ intHeight p ≤ H ∧
        x = NormedSpace.normalize (intVector B p) := Iff.rfl

/-- The real height of an integral direction is the cast of a natural
number, namely the maximum of its two natural absolute values. -/
theorem intHeight_eq_natMaxAbs_cast (p : ℤ × ℤ) :
    intHeight p = ((max p.1.natAbs p.2.natAbs : ℕ) : ℝ) := by
  simp [intHeight, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]

/-- A real height bound on an integral direction is exactly its natural
floor bound when the cutoff is nonnegative. -/
theorem intHeight_le_iff_le_natFloor (p : ℤ × ℤ) (H : ℝ) (hH : 0 ≤ H) :
    intHeight p ≤ H ↔ intHeight p ≤ (⌊H⌋₊ : ℝ) := by
  rw [intHeight_eq_natMaxAbs_cast, Nat.cast_le]
  exact (Nat.le_floor_iff hH).symm

/-- At nonnegative real heights, the actual primitive cutoff agrees
exactly with the existing finite cutoff at the natural floor. -/
theorem realCutoffCorners_eq_natFloor (B : Module.Basis (Fin 2) ℝ E)
    (H : ℝ) (hH : 0 ≤ H) :
    realCutoffCorners B H = (↑(cutoffCorners B ⌊H⌋₊) : Set E) := by
  classical
  ext x
  constructor
  · rintro ⟨p, hp, hh, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨p, (mem_primitiveDirectionsUpTo ⌊H⌋₊ p).mpr
      ⟨hp, (intHeight_le_iff_le_natFloor p H hH).mp hh⟩, rfl⟩
  · intro hx
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    obtain ⟨hcop, hh⟩ := (mem_primitiveDirectionsUpTo ⌊H⌋₊ p).mp hp
    exact ⟨p, hcop, (intHeight_le_iff_le_natFloor p H hH).mpr hh, hpx.symm⟩

/-- The real cutoff specializes to the previous cutoff at natural heights. -/
theorem realCutoffCorners_nat (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) :
    realCutoffCorners B (H : ℝ) = (↑(cutoffCorners B H) : Set E) := by
  simpa using realCutoffCorners_eq_natFloor B (H : ℝ) (Nat.cast_nonneg H)

theorem realCutoffCorners_eq_empty_of_neg (B : Module.Basis (Fin 2) ℝ E)
    (H : ℝ) (hH : H < 0) : realCutoffCorners B H = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨p, _, hh, _⟩
  exact (not_le_of_gt hH) ((intHeight_nonneg p).trans hh)

/-- The real primitive height cutoff is a finite set for every real height. -/
theorem realCutoffCorners_finite (B : Module.Basis (Fin 2) ℝ E) (H : ℝ) :
    (realCutoffCorners B H).Finite := by
  by_cases hH : 0 ≤ H
  · rw [realCutoffCorners_eq_natFloor B H hH]
    exact (cutoffCorners B ⌊H⌋₊).finite_toSet
  · rw [realCutoffCorners_eq_empty_of_neg B H (lt_of_not_ge hH)]
    exact Set.finite_empty

end Markov
