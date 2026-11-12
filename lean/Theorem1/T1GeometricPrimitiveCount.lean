import T1MobiusFinite
import Markov.IntrinsicMcShaneRivinCount

/-! Primitive points are defined in the independently constructed geometric
ball. Finite Möbius inversion is then applied to its actual lattice points. -/

noncomputable section
open Classical Finset Set
open scoped ArithmeticFunction.Moebius

namespace Markov

def t1_geometricNonzeroCoordinates (R : ℝ) : Set (ℤ × ℤ) :=
  {p | p ≠ (0, 0) ∧ p ∈ modularMcShaneRivinCoordinateSet R}

def t1_geometricPrimitiveCoordinates (R : ℝ) : Set (ℤ × ℤ) :=
  {p | IsCoprime p.1 p.2 ∧ p ∈ modularMcShaneRivinCoordinateSet R}

def t1_geometricPrimitiveCount (R : ℝ) : ℕ :=
  (t1_geometricPrimitiveCoordinates R).ncard

theorem t1_geometricNonzeroCoordinates_finite (R : ℝ) (hR : 0 < R) :
    (t1_geometricNonzeroCoordinates R).Finite :=
  (modularMcShaneRivinCoordinateSet_finite R hR).subset (fun _ hp => hp.2)

theorem t1_geometricPrimitiveCoordinates_finite (R : ℝ) (hR : 0 < R) :
    (t1_geometricPrimitiveCoordinates R).Finite :=
  (modularMcShaneRivinCoordinateSet_finite R hR).subset (fun _ hp => hp.2)

/-- The actual finite nonzero points used in the inversion, not a supplied
counting model or a trace-ball definition. -/
def t1_geometricNonzeroFinset (R : ℝ) (hR : 0 < R) : Finset (ℤ × ℤ) :=
  (t1_geometricNonzeroCoordinates_finite R hR).toFinset

@[simp] theorem t1_mem_geometricNonzeroFinset (R : ℝ) (hR : 0 < R) (p : ℤ × ℤ) :
    p ∈ t1_geometricNonzeroFinset R hR ↔
      p ≠ (0, 0) ∧ p ∈ modularMcShaneRivinCoordinateSet R := by
  simp [t1_geometricNonzeroFinset, t1_geometricNonzeroCoordinates]

theorem t1_primitive_finset_actual (R : ℝ) (hR : 0 < R) :
    (((t1_geometricNonzeroFinset R hR).filter (fun p => IsCoprime p.1 p.2)) :
      Set (ℤ × ℤ)) = t1_geometricPrimitiveCoordinates R := by
  ext p
  simp only [Finset.mem_coe, Finset.mem_filter, t1_mem_geometricNonzeroFinset,
    t1_geometricPrimitiveCoordinates, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨_, hmem⟩, hprim⟩
    exact ⟨hprim, hmem⟩
  · rintro ⟨hprim, hmem⟩
    exact ⟨⟨coprime_integerPair_ne_zero hprim, hmem⟩, hprim⟩

theorem t1_geometricPrimitiveCount_eq_filter_card (R : ℝ) (hR : 0 < R) :
    t1_geometricPrimitiveCount R =
      ((t1_geometricNonzeroFinset R hR).filter (fun p => IsCoprime p.1 p.2)).card := by
  rw [t1_geometricPrimitiveCount, ← t1_primitive_finset_actual R hR,
    Set.ncard_coe_finset]

/-- An exact finite Möbius formula for the genuine geometric primitive
count. The divisor cutoff is computed from the actual nonzero point set.
No Mertens bound, asymptotic estimate, or correspondence field is assumed. -/
theorem t1_geometricPrimitiveCount_moebius_fibers (R : ℝ) (hR : 0 < R) :
    (t1_geometricPrimitiveCount R : ℤ) =
      ∑ g ∈ Finset.Icc 1 (t1_gcdCutoff (t1_geometricNonzeroFinset R hR)),
        μ g * (((t1_geometricNonzeroFinset R hR).filter
          (fun p => g ∣ Int.gcd p.1 p.2)).card : ℤ) := by
  rw [t1_geometricPrimitiveCount_eq_filter_card R hR]
  apply t1_finite_primitive_count_divisor_fibers
  intro p hp
  exact ((t1_mem_geometricNonzeroFinset R hR p).mp hp).1

end Markov
