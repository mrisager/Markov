import Markov.FiniteAngularPacking
import Markov.FiniteReciprocalCounting

/-! Inverse-length partial summation for primitive directions assigned to
one actual unresolved component. The component packing estimate is proved,
and the angular width may be replaced by the actual exponential turn tail. -/

noncomputable section
open Set MeasureTheory
namespace Markov

/-- The actual primitive-component reciprocal-length bound, with the
component's own finite turn retained explicitly. -/
theorem trace_component_sum_inv_le (D : Finset (ℤ × ℤ)) (L K H η : ℝ)
    (hL : 0 < L) (hLK : L ≤ K) (hH : 1 ≤ H) (hη : 0 ≤ η)
    (x : TracePlane) (hx : x ∈ traceUncutBoundary H)
    (hprimitive : ∀ d ∈ D, IsCoprime d.1 d.2)
    (hannulus : ∀ d ∈ D, L ≤ intEuclidean d ∧ intEuclidean d ≤ K)
    (hmem : ∀ d ∈ D, NormedSpace.normalize (euclideanIntDirection d) ∈
      closedAngularNeighborhood
        (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η) :
    ∑ d ∈ D, 1 / intEuclidean d ≤ 1 / L +
      2 * ((traceBoundaryTurn (connectedComponentIn (traceUncutBoundary H) x)).toReal +
        2 * η) * K := by
  classical
  let α := (traceBoundaryTurn (connectedComponentIn (traceUncutBoundary H) x)).toReal + 2 * η
  have hα : 0 ≤ α := add_nonneg ENNReal.toReal_nonneg (mul_nonneg (by norm_num) hη)
  have hcount (T : ℝ) (_hLT : L ≤ T) (_hTK : T ≤ K) :
      ((D.filter fun d => intEuclidean d ≤ T).card : ℝ) ≤ 1 * (1 + α * T ^ 2) := by
    by_cases hT : 1 ≤ T
    · simpa only [one_mul, α] using
        primitive_finset_card_le_trace_component_neighborhood
          (D.filter fun d => intEuclidean d ≤ T) T H η hT hH hη x hx
          (fun d hd => hprimitive d (Finset.mem_filter.mp hd).1)
          (fun _ hd => (Finset.mem_filter.mp hd).2)
          (fun d hd => hmem d (Finset.mem_filter.mp hd).1)
    · have hempty : (D.filter fun d => intEuclidean d ≤ T) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro d hd
        have hdD := (Finset.mem_filter.mp hd).1
        have hdT := (Finset.mem_filter.mp hd).2
        have hone := intEuclidean_ge_one d (primitiveIntDirection_ne_zero d (hprimitive d hdD))
        linarith
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero, one_mul]
      positivity
  simpa only [one_div, one_mul, mul_one, α] using
    finite_sum_inv_le_of_count_quadratic D intEuclidean 1 α L K hL hLK
      (by norm_num) hα hannulus hcount

theorem trace_component_sum_inv_le_of_turn_bound
    (D : Finset (ℤ × ℤ)) (L K H η A : ℝ)
    (hL : 0 < L) (hLK : L ≤ K) (hH : 1 ≤ H) (hη : 0 ≤ η)
    (x : TracePlane) (hx : x ∈ traceUncutBoundary H)
    (hprimitive : ∀ d ∈ D, IsCoprime d.1 d.2)
    (hannulus : ∀ d ∈ D, L ≤ intEuclidean d ∧ intEuclidean d ≤ K)
    (hmem : ∀ d ∈ D, NormedSpace.normalize (euclideanIntDirection d) ∈
      closedAngularNeighborhood
        (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η)
    (hA : (traceBoundaryTurn (connectedComponentIn (traceUncutBoundary H) x)).toReal ≤ A) :
    ∑ d ∈ D, 1 / intEuclidean d ≤ 1 / L + 2 * (A + 2 * η) * K := by
  apply (trace_component_sum_inv_le D L K H η hL hLK hH hη x hx
    hprimitive hannulus hmem).trans
  have hK : 0 ≤ K := hL.le.trans hLK
  gcongr

/-- Uniform exponential turn decay supplies the same reciprocal bound
for every actual component; no width estimate is assumed. -/
theorem trace_component_sum_inv_le_exp_width :
    ∃ M κ : ℝ, 0 < M ∧ 0 < κ ∧
      ∀ (D : Finset (ℤ × ℤ)) (L K H η : ℝ),
      0 < L → L ≤ K → 1 ≤ H → 0 ≤ η →
      ∀ x : TracePlane, x ∈ traceUncutBoundary H →
      (∀ d ∈ D, IsCoprime d.1 d.2) →
      (∀ d ∈ D, L ≤ intEuclidean d ∧ intEuclidean d ≤ K) →
      (∀ d ∈ D, NormedSpace.normalize (euclideanIntDirection d) ∈
        closedAngularNeighborhood
          (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η) →
      ∑ d ∈ D, 1 / intEuclidean d ≤
        1 / L + 2 * (M * Real.exp (-(κ * H)) + 2 * η) * K := by
  obtain ⟨M, κ, hM, hκ, htail⟩ := traceBoundary_turn_tail_real
  refine ⟨M, κ, hM, hκ, ?_⟩
  intro D L K H η hL hLK hH hη x hx hprimitive hannulus hmem
  apply trace_component_sum_inv_le_of_turn_bound D L K H η _ hL hLK hH hη x hx
    hprimitive hannulus hmem
  have hc : (traceBoundaryTurn (connectedComponentIn (traceUncutBoundary H) x)).toReal ≤
      (traceBoundaryTurn (traceUncutBoundary H)).toReal :=
    ENNReal.toReal_mono (measure_ne_top traceBoundaryTurn _)
      (measure_mono (connectedComponentIn_subset (traceUncutBoundary H) x))
  exact hc.trans (htail H hH)

end Markov
