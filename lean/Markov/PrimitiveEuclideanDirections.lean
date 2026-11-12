import Markov.FiniteLatticeReciprocalSquare
import Markov.PrimitiveUnresolvedSet
import Markov.PrimitiveAngularSpacing

/-! Exact finite primitive Euclidean direction sets for Corollary 11. -/

noncomputable section
open Classical
namespace Markov

/-- All signed primitive integer directions in the original Euclidean ball. -/
def primitiveEuclideanDirectionsUpTo (K : ℝ) : Finset (ℤ × ℤ) :=
  (integerDirectionsEuclideanUpTo K).filter (fun d => IsCoprime d.1 d.2)

@[simp] theorem mem_primitiveEuclideanDirectionsUpTo (K : ℝ) (d : ℤ × ℤ) :
    d ∈ primitiveEuclideanDirectionsUpTo K ↔
      IsCoprime d.1 d.2 ∧ intEuclidean d ≤ K := by
  simp only [primitiveEuclideanDirectionsUpTo, Finset.mem_filter,
    mem_integerDirectionsEuclideanUpTo]
  constructor
  · rintro ⟨⟨_, hs⟩, hp⟩
    exact ⟨hp, hs⟩
  · rintro ⟨hp, hs⟩
    exact ⟨⟨primitiveIntDirection_ne_zero d hp, hs⟩, hp⟩

/-- Filtering the exact full primitive set recovers the previously checked
full unresolved set, including its original cutoff convention. -/
theorem primitiveEuclideanDirectionsUpTo_filter_unresolved (K H η : ℝ) :
    (primitiveEuclideanDirectionsUpTo K).filter (fun d => IsTraceUnresolved d K H η) =
      primitiveUnresolvedUpTo K H η K := by
  ext d
  simp only [Finset.mem_filter, mem_primitiveEuclideanDirectionsUpTo,
    mem_primitiveUnresolvedUpTo]
  exact and_assoc

theorem primitiveEuclideanDirectionsUpTo_reciprocal_square_le_log
    (K : ℝ) (hK : 1 ≤ K) :
    (∑ d ∈ primitiveEuclideanDirectionsUpTo K, 1 / intEuclidean d ^ 2) ≤
      50 * Real.log (2 * K) := by
  apply finite_integer_reciprocal_square_le_log _ K hK
  · intro d hd
    exact primitiveIntDirection_ne_zero d ((mem_primitiveEuclideanDirectionsUpTo K d).mp hd).1
  · intro d hd
    exact ((mem_primitiveEuclideanDirectionsUpTo K d).mp hd).2

end Markov
