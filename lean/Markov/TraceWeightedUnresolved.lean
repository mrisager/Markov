import Markov.TraceLemmaSeven
import Markov.TraceUnresolvedArcLength
import Markov.WeightedLogarithmicCount

/-! The weighted unresolved estimate (83), for the constructed trace
ball and its actual chosen component variations. The uniform count in
Lemma 7 and the size estimate in Lemma 6 are combined by summation by
parts. All geometry/counting inputs are proved for this trace ball. -/

noncomputable section
namespace Markov

/-- Filtering the full unresolved set by another Euclidean radius gives
exactly the actual primitive unresolved set at that radius. -/
theorem primitiveUnresolvedUpTo_self_filter (K H η T : ℝ) :
    (primitiveUnresolvedUpTo K H η K).filter (fun d => intEuclidean d ≤ T) =
      primitiveUnresolvedUpTo K H η T := by
  classical
  ext d
  rw [Finset.mem_filter, mem_primitiveUnresolvedUpTo, mem_primitiveUnresolvedUpTo]
  constructor
  · rintro ⟨⟨hp, _, hu⟩, hT⟩
    exact ⟨hp, hT, hu⟩
  · rintro ⟨hp, hT, hu⟩
    exact ⟨⟨hp, hu.2.1, hu⟩, hT⟩

/-- Dividing the actual Lemma 6 size scale by the direction length gives
the inverse-square-root weight used in summation by parts. -/
theorem div_le_inv_sqrt_of_sqrt_bound (s C B D : ℝ)
    (hB : 0 < B) (hD : 0 < D) (hs : s ≤ C * Real.sqrt D / B) :
    s / D ≤ (C / B) / Real.sqrt D := by
  have hsqrt : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  apply (div_le_div_of_nonneg_right hs hD.le).trans_eq
  apply (div_eq_div_iff hD.ne' hsqrt.ne').2
  field_simp
  rw [Real.sq_sqrt hD.le]

/-- The paper's weighted estimate (83) for the full finite set of actual
primitive unresolved directions. Arc sizes are the actual finite
Euclidean radial variations of their associated components. -/
theorem trace_weighted_unresolved_bound :
    ∃ D C : ℝ, 0 < D ∧ 0 < C ∧
      ∀ (K H ε η : ℝ), 1 ≤ H → 0 < ε → 0 < η →
      (2 + ε) * η ≤ traceCornerLowerConstant *
        Real.exp (-(2 * traceAxisLength) * H) →
      D * Real.log (2 * K) ≤ H →
      (∑ d ∈ primitiveUnresolvedUpTo K H η K,
        traceUnresolvedArcLength d K H η / intEuclidean d) ≤
          C / (H * Real.sqrt H) := by
  obtain ⟨D, Ccount, hD, hCcount, hcount⟩ := trace_lemma7
  obtain ⟨Ca, hCa, hsize⟩ := exists_traceUnresolvedArcLength_bound
  refine ⟨D, (256 * Ccount) * Ca, hD, by positivity, ?_⟩
  intro K H ε η hH hε hη hbasic hcutoff
  have hHpos : 0 < H := by linarith
  have hden : 0 < H * Real.sqrt H := mul_pos hHpos (Real.sqrt_pos.mpr hHpos)
  have hr : ∀ d ∈ primitiveUnresolvedUpTo K H η K, 1 ≤ intEuclidean d := by
    intro d hd
    exact intEuclidean_ge_one d ((mem_primitiveUnresolvedUpTo K H η K d).mp hd).2.2.1
  have hc : ∀ T : ℝ, 1 ≤ T →
      (((primitiveUnresolvedUpTo K H η K).filter
        (fun d => intEuclidean d ≤ T)).card : ℝ) ≤ Ccount * Real.log (2 * T) ^ 2 := by
    intro T hT
    rw [primitiveUnresolvedUpTo_self_filter]
    exact hcount K H ε η T hT hε hη hbasic hcutoff
  have hw : ∀ d ∈ primitiveUnresolvedUpTo K H η K,
      traceUnresolvedArcLength d K H η / intEuclidean d ≤
        (Ca / (H * Real.sqrt H)) / Real.sqrt (intEuclidean d) := by
    intro d hd
    have hu := ((mem_primitiveUnresolvedUpTo K H η K d).mp hd).2.2
    exact div_le_inv_sqrt_of_sqrt_bound _ Ca _ _ hden
      (lt_of_lt_of_le zero_lt_one (hr d hd))
      (hsize K H ε η d hH hε hbasic hu)
  have hsum := finite_sum_le_of_count_log_square
    (primitiveUnresolvedUpTo K H η K) intEuclidean
    (fun d => traceUnresolvedArcLength d K H η / intEuclidean d)
    Ccount (Ca / (H * Real.sqrt H)) hr hCcount.le (by positivity) hc hw
  convert hsum using 1
  ring

end Markov
