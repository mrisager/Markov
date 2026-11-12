import Markov.FareyScale
import Markov.TraceUnresolvedAssociation
import Mathlib.Data.Set.Card

/-! The actual finite set of primitive unresolved integral directions,
with the Euclidean size restriction retained exactly. The enclosing
integral square is only used to construct a finset; its height bound adds
no restriction to the resulting set. -/

noncomputable section
namespace Markov

/-- Maximum coordinate height is bounded by actual Euclidean length. -/
theorem intHeight_le_intEuclidean (d : ℤ × ℤ) : intHeight d ≤ intEuclidean d := by
  exact max_le (intEuclidean_coordinate_bounds d).1
    (intEuclidean_coordinate_bounds d).2

/-- All primitive directions of Euclidean size at most `T` that satisfy
the actual-component unresolved predicate. -/
def primitiveUnresolvedUpTo (K H η T : ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact (primitiveDirectionsUpTo ⌈T⌉₊).filter
    (fun d => intEuclidean d ≤ T ∧ IsTraceUnresolved d K H η)

/-- Exact membership has no additional maximum-coordinate restriction,
including when the real size bound is negative. -/
theorem mem_primitiveUnresolvedUpTo (K H η T : ℝ) (d : ℤ × ℤ) :
    d ∈ primitiveUnresolvedUpTo K H η T ↔
      IsCoprime d.1 d.2 ∧ intEuclidean d ≤ T ∧ IsTraceUnresolved d K H η := by
  classical
  simp only [primitiveUnresolvedUpTo, Finset.mem_filter, mem_primitiveDirectionsUpTo]
  constructor
  · rintro ⟨⟨hcop, _⟩, hsize, hunresolved⟩
    exact ⟨hcop, hsize, hunresolved⟩
  · rintro ⟨hcop, hsize, hunresolved⟩
    refine ⟨⟨hcop, ?_⟩, hsize, hunresolved⟩
    exact (intHeight_le_intEuclidean d).trans (hsize.trans (Nat.le_ceil T))

/-- The actual primitive unresolved set with an exact Euclidean cutoff. -/
def primitiveUnresolvedSet (K H η T : ℝ) : Set (ℤ × ℤ) :=
  {d | IsCoprime d.1 d.2 ∧ intEuclidean d ≤ T ∧ IsTraceUnresolved d K H η}

theorem coe_primitiveUnresolvedUpTo (K H η T : ℝ) :
    (↑(primitiveUnresolvedUpTo K H η T) : Set (ℤ × ℤ)) =
      primitiveUnresolvedSet K H η T := by
  ext d
  exact mem_primitiveUnresolvedUpTo K H η T d

theorem finite_primitiveUnresolvedSet (K H η T : ℝ) :
    (primitiveUnresolvedSet K H η T).Finite := by
  rw [← coe_primitiveUnresolvedUpTo K H η T]
  exact Finset.finite_toSet _

theorem ncard_primitiveUnresolvedSet (K H η T : ℝ) :
    (primitiveUnresolvedSet K H η T).ncard =
      (primitiveUnresolvedUpTo K H η T).card := by
  rw [← coe_primitiveUnresolvedUpTo K H η T, Set.ncard_coe_finset]

/-- Increasing only the Euclidean cutoff preserves actual membership. -/
theorem primitiveUnresolvedUpTo_mono_size (K H η : ℝ) {S T : ℝ} (hST : S ≤ T) :
    primitiveUnresolvedUpTo K H η S ⊆ primitiveUnresolvedUpTo K H η T := by
  intro d hd
  obtain ⟨hcop, hsize, hunresolved⟩ := (mem_primitiveUnresolvedUpTo K H η S d).mp hd
  exact (mem_primitiveUnresolvedUpTo K H η T d).mpr
    ⟨hcop, hsize.trans hST, hunresolved⟩

theorem primitiveUnresolvedUpTo_card_le_square (K H η T : ℝ) :
    (primitiveUnresolvedUpTo K H η T).card ≤ (2 * ⌈T⌉₊ + 1) ^ 2 := by
  classical
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (primitiveDirectionsUpTo_card_le ⌈T⌉₊)

theorem primitiveUnresolvedUpTo_eq_empty_of_lt_one (K H η T : ℝ) (hT : T < 1) :
    primitiveUnresolvedUpTo K H η T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  obtain ⟨_, hsize, hunresolved⟩ := (mem_primitiveUnresolvedUpTo K H η T d).mp hd
  exact (not_le_of_gt hT) ((intEuclidean_ge_one d hunresolved.1).trans hsize)

/-- At `T = K` the additional size cutoff is already part of the
unresolved predicate, so this is the complete primitive unresolved set. -/
theorem coe_primitiveUnresolvedUpTo_self (K H η : ℝ) :
    (↑(primitiveUnresolvedUpTo K H η K) : Set (ℤ × ℤ)) =
      {d | IsCoprime d.1 d.2 ∧ IsTraceUnresolved d K H η} := by
  ext d
  rw [Finset.mem_coe, mem_primitiveUnresolvedUpTo]
  constructor
  · rintro ⟨hcop, _, hunresolved⟩
    exact ⟨hcop, hunresolved⟩
  · rintro ⟨hcop, hunresolved⟩
    exact ⟨hcop, hunresolved.2.1, hunresolved⟩

theorem finite_primitive_traceUnresolved (K H η : ℝ) :
    {d : ℤ × ℤ | IsCoprime d.1 d.2 ∧ IsTraceUnresolved d K H η}.Finite := by
  rw [← coe_primitiveUnresolvedUpTo_self K H η]
  exact Finset.finite_toSet _

theorem ncard_primitive_traceUnresolved (K H η : ℝ) :
    {d : ℤ × ℤ | IsCoprime d.1 d.2 ∧ IsTraceUnresolved d K H η}.ncard =
      (primitiveUnresolvedUpTo K H η K).card := by
  rw [← coe_primitiveUnresolvedUpTo_self K H η, Set.ncard_coe_finset]

end Markov
