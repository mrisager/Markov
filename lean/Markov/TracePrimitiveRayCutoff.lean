import Markov.TracePrimitiveRayPoisson
import Markov.PrimitiveEuclideanDirections

/-! Cutting off signed primitive rays preserves every multiple in the head.
Only rays whose primitive part is long are bounded by the full individual
frequency tail; absolute convergence justifies each comparison. -/

noncomputable section
open Classical
namespace Markov

private theorem intEuclidean_positive_multiple_ge (k : ℤ × ℤ) (m : ℕ) :
    intEuclidean k ≤ intEuclidean (((m : ℤ) + 1) • k) := by
  rw [← euclideanIntDirection_norm k, ← euclideanIntDirection_norm,
    euclideanIntDirection_zsmul, norm_smul, Real.norm_eq_abs]
  have hm : (0 : ℝ) ≤ ((m : ℤ) + 1 : ℤ) := by positivity
  rw [abs_of_nonneg hm]
  push_cast
  nlinarith [norm_nonneg (euclideanIntDirection k)]

/-- The actual smoothed discrepancy is bounded by complete blocks on all
short signed primitive rays and the individual full-lattice frequency tail.
There is no factor two: both primitive signs are already retained. -/
theorem trace_smoothed_lattice_discrepancy_primitive_cutoff_bound
    (S Q K : ℝ) (hS : 0 < S) (hQ : 0 < Q) (hK : 1 ≤ K) :
    |traceSmoothedLatticeCount S Q - S ^ 2 * traceEuclideanArea| ≤
      (∑ d ∈ primitiveEuclideanDirectionsUpTo K, ‖traceRadialBlock S Q d‖) +
      ∑' n : ℤ × ℤ, if K < intEuclidean n then
        ‖traceFourierLatticeTerm S Q n‖ else 0 := by
  let f := traceFourierLatticeTerm S Q
  let g : ℤ × ℤ → ℝ := fun n => if K < intEuclidean n then ‖f n‖ else 0
  have hf : Summable (fun n : ℤ × ℤ => ‖f n‖) :=
    traceFourierLatticeTerm_norm_summable S Q hS hQ
  have hg : Summable g := by
    apply hf.of_nonneg_of_le
    · intro n
      dsimp [g]
      split_ifs <;> positivity
    · intro n
      dsimp [g]
      split_ifs <;> simp [norm_nonneg]
  have hprod : Summable (fun p : PrimitiveIntegerRay × ℕ =>
      g (((p.2 : ℤ) + 1) • p.1.1)) := by
    have hh := (hg.subtype (fun n : ℤ × ℤ => n ≠ (0, 0))).comp_injective
      primitiveRayNatEquiv.symm.injective
    simpa only [primitiveRayNatEquiv_symm_val] using hh
  have hzero : g (0, 0) = 0 := by
    dsimp [g]
    have hn : ¬ K < intEuclidean (0, 0) := by simp [intEuclidean]; linarith
    rw [if_neg hn]
  have hnonzero : (∑' n : NonzeroIntegerDirection, g n.1) = ∑' n : ℤ × ℤ, g n := by
    have hh := hg.sum_add_tsum_subtype_compl ({(0, 0)} : Finset (ℤ × ℤ))
    have hpred : (fun n : ℤ × ℤ => n ∉ ({(0, 0)} : Finset (ℤ × ℤ))) =
        (fun n => n ≠ (0, 0)) := by
      funext n
      apply propext
      simp
    simp only [Finset.sum_singleton] at hh
    change g (0, 0) +
      (∑' n : {n : ℤ × ℤ // n ∉ ({(0, 0)} : Finset (ℤ × ℤ))}, g n.1) =
        ∑' n : ℤ × ℤ, g n at hh
    rw [hpred] at hh
    simpa only [hzero, zero_add] using hh
  have hregroup : (∑' k : PrimitiveIntegerRay, ∑' m : ℕ,
      g (((m : ℤ) + 1) • k.1)) = ∑' n : ℤ × ℤ, g n := by
    calc
      _ = ∑' p : PrimitiveIntegerRay × ℕ, g (((p.2 : ℤ) + 1) • p.1.1) :=
        hprod.tsum_prod.symm
      _ = ∑' n : NonzeroIntegerDirection, g n.1 := by
        simpa only [primitiveRayNatEquiv_symm_val] using
          primitiveRayNatEquiv.symm.tsum_eq (fun n : NonzeroIntegerDirection => g n.1)
      _ = _ := hnonzero
  let A : Finset PrimitiveIntegerRay := (primitiveEuclideanDirectionsUpTo K).subtype
    (fun d : ℤ × ℤ => IsCoprime d.1 d.2)
  have hAmem (k : PrimitiveIntegerRay) : k ∈ A ↔ intEuclidean k.1 ≤ K := by
    simp only [A, Finset.mem_subtype, mem_primitiveEuclideanDirectionsUpTo,
      and_iff_right k.2]
  let head : PrimitiveIntegerRay → ℝ := fun k =>
    if intEuclidean k.1 ≤ K then ‖traceRadialBlock S Q k.1‖ else 0
  have hblock := traceRadialBlock_primitive_norm_summable S Q hS hQ
  have hhead : Summable head := by
    apply hblock.of_nonneg_of_le
    · intro k
      dsimp [head]
      split_ifs <;> positivity
    · intro k
      dsimp [head]
      split_ifs <;> simp [norm_nonneg]
  have hheadsum : (∑' k : PrimitiveIntegerRay, head k) =
      ∑ d ∈ primitiveEuclideanDirectionsUpTo K, ‖traceRadialBlock S Q d‖ := by
    calc
      _ = ∑ k ∈ A, head k := by
        apply tsum_eq_sum
        intro k hk
        exact if_neg (fun hh => hk ((hAmem k).mpr hh))
      _ = ∑ k ∈ A, ‖traceRadialBlock S Q k.1‖ := by
        apply Finset.sum_congr rfl
        intro k hk
        exact if_pos ((hAmem k).mp hk)
      _ = _ := Finset.sum_subtype_of_mem (fun d => ‖traceRadialBlock S Q d‖)
        (fun d hd => ((mem_primitiveEuclideanDirectionsUpTo K d).mp hd).1)
  have hpoint (k : PrimitiveIntegerRay) : ‖traceRadialBlock S Q k.1‖ ≤
      head k + ∑' m : ℕ, g (((m : ℤ) + 1) • k.1) := by
    by_cases hk : intEuclidean k.1 ≤ K
    · dsimp [head]
      rw [if_pos hk]
      exact le_add_of_nonneg_right (tsum_nonneg (fun m => by
        dsimp [g]
        split_ifs <;> positivity))
    · have hlong (m : ℕ) : K < intEuclidean (((m : ℤ) + 1) • k.1) :=
        (lt_of_not_ge hk).trans_le (intEuclidean_positive_multiple_ge k.1 m)
      calc
        _ = ‖∑' m : ℕ, f (((m : ℤ) + 1) • k.1)‖ := by
          rw [traceRadialBlock_eq_tsum_latticeTerms]
        _ ≤ ∑' m : ℕ, ‖f (((m : ℤ) + 1) • k.1)‖ :=
          norm_tsum_le_tsum_norm (primitiveRay_inner_norm_summable hf k)
        _ = _ := by simp only [head, if_neg hk, g, if_pos (hlong _), zero_add]
  have hsum := hblock.tsum_le_tsum hpoint (hhead.add hprod.prod)
  rw [hhead.tsum_add hprod.prod, hheadsum, hregroup] at hsum
  exact (trace_smoothed_lattice_discrepancy_primitiveRay_bound S Q hS hQ).trans hsum

end Markov
