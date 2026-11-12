import Markov.TraceWeightedUnresolved

/-! Transport of actual unresolved directions and their chosen component
variations when only the direction-size cutoff changes. The small weighted
estimate retains the logarithmic hypothesis at the minimum cutoff. -/

noncomputable section
open Set

namespace Markov

/-- Changing the external direction-size cutoff does not change geometric
unresolved membership for a direction lying below both cutoffs. -/
theorem isTraceUnresolved_cutoff_iff {d : ℤ × ℤ} {K K' H η : ℝ}
    (hdK : intEuclidean d ≤ K) (hdK' : intEuclidean d ≤ K') :
    IsTraceUnresolved d K H η ↔ IsTraceUnresolved d K' H η := by
  constructor
  · intro h
    exact ⟨h.1, hdK', h.2.2⟩
  · intro h
    exact ⟨h.1, hdK, h.2.2⟩

/-- The component-data type is independent of the external size cutoff.
Consequently the choice is identical whenever it is defined at both cutoffs. -/
theorem traceUnresolvedComponentData_cutoff_eq (d : ℤ × ℤ) (K K' H η : ℝ)
    (h : IsTraceUnresolved d K H η ∧ 1 ≤ H)
    (h' : IsTraceUnresolved d K' H η ∧ 1 ≤ H) :
    traceUnresolvedComponentData d K H η h = traceUnresolvedComponentData d K' H η h' := by
  rfl

/-- The selected actual component is unchanged by an admissible size-cutoff change. -/
theorem traceUnresolvedComponent_cutoff_eq {d : ℤ × ℤ} {K K' H η : ℝ}
    (hdK : intEuclidean d ≤ K) (hdK' : intEuclidean d ≤ K') :
    traceUnresolvedComponent d K H η = traceUnresolvedComponent d K' H η := by
  classical
  have hu : IsTraceUnresolved d K H η ↔ IsTraceUnresolved d K' H η :=
    isTraceUnresolved_cutoff_iff hdK hdK'
  by_cases h : IsTraceUnresolved d K H η ∧ 1 ≤ H
  · have h' : IsTraceUnresolved d K' H η ∧ 1 ≤ H := ⟨hu.mp h.1, h.2⟩
    simp only [traceUnresolvedComponent, dif_pos h, dif_pos h']
    rfl
  · have h' : ¬(IsTraceUnresolved d K' H η ∧ 1 ≤ H) := by
      intro hh
      exact h ⟨hu.mpr hh.1, hh.2⟩
    simp only [traceUnresolvedComponent, dif_neg h, dif_neg h']

/-- The actual chosen finite component variation is unchanged by an
admissible direction-size cutoff change, including the zero fallback. -/
theorem traceUnresolvedArcLength_cutoff_eq {d : ℤ × ℤ} {K K' H η : ℝ}
    (hdK : intEuclidean d ≤ K) (hdK' : intEuclidean d ≤ K') :
    traceUnresolvedArcLength d K H η = traceUnresolvedArcLength d K' H η := by
  classical
  have hu : IsTraceUnresolved d K H η ↔ IsTraceUnresolved d K' H η :=
    isTraceUnresolved_cutoff_iff hdK hdK'
  by_cases h : IsTraceUnresolved d K H η ∧ 1 ≤ H
  · have h' : IsTraceUnresolved d K' H η ∧ 1 ≤ H := ⟨hu.mp h.1, h.2⟩
    simp only [traceUnresolvedArcLength, dif_pos h, dif_pos h']
    rfl
  · have h' : ¬(IsTraceUnresolved d K' H η ∧ 1 ≤ H) := by
      intro hh
      exact h ⟨hu.mpr hh.1, hh.2⟩
    simp only [traceUnresolvedArcLength, dif_neg h, dif_neg h']

/-- Filtering the full primitive unresolved set by another radius is
exactly the full unresolved set at the minimum of the two radii. -/
theorem primitiveUnresolvedUpTo_filter_min (K L H η : ℝ) :
    (primitiveUnresolvedUpTo K H η K).filter (fun d ↦ intEuclidean d ≤ L) =
      primitiveUnresolvedUpTo (min K L) H η (min K L) := by
  classical
  ext d
  rw [Finset.mem_filter, mem_primitiveUnresolvedUpTo, mem_primitiveUnresolvedUpTo]
  constructor
  · rintro ⟨⟨hp, hdK, hu⟩, hdL⟩
    have hdmin := le_min hdK hdL
    exact ⟨hp, hdmin, (isTraceUnresolved_cutoff_iff hdK hdmin).mp hu⟩
  · rintro ⟨hp, hdmin, hu⟩
    have hdK := hdmin.trans (min_le_left K L)
    exact ⟨⟨hp, hdK, (isTraceUnresolved_cutoff_iff hdmin hdK).mp hu⟩,
      hdmin.trans (min_le_right K L)⟩

/-- Both membership and the actual chosen arc weight transport to the
minimum cutoff in the small-direction contribution. -/
theorem trace_unresolved_small_weighted_sum_eq (K L H η : ℝ) :
    (∑ d ∈ (primitiveUnresolvedUpTo K H η K).filter (fun d ↦ intEuclidean d ≤ L),
      traceUnresolvedArcLength d K H η / intEuclidean d) =
      ∑ d ∈ primitiveUnresolvedUpTo (min K L) H η (min K L),
        traceUnresolvedArcLength d (min K L) H η / intEuclidean d := by
  rw [primitiveUnresolvedUpTo_filter_min]
  apply Finset.sum_congr rfl
  intro d hd
  have hm := ((mem_primitiveUnresolvedUpTo (min K L) H η (min K L) d).mp hd).2.1
  rw [traceUnresolvedArcLength_cutoff_eq (hm.trans (min_le_left K L)) hm]

/-- Weighted estimate (83) applies to the small-direction contribution
under its logarithmic hypothesis at `min K L`, rather than at the full cutoff. -/
theorem trace_unresolved_small_weighted_bound :
    ∃ D C : ℝ, 0 < D ∧ 0 < C ∧
      ∀ (K L H ε η : ℝ), 1 ≤ H → 0 < ε → 0 < η →
      (2 + ε) * η ≤ traceCornerLowerConstant *
        Real.exp (-(2 * traceAxisLength) * H) →
      D * Real.log (2 * min K L) ≤ H →
      (∑ d ∈ (primitiveUnresolvedUpTo K H η K).filter (fun d ↦ intEuclidean d ≤ L),
        traceUnresolvedArcLength d K H η / intEuclidean d) ≤ C / (H * Real.sqrt H) := by
  obtain ⟨D, C, hD, hC, hbound⟩ := trace_weighted_unresolved_bound
  refine ⟨D, C, hD, hC, ?_⟩
  intro K L H ε η hH hε hη hbasic hcutoff
  rw [trace_unresolved_small_weighted_sum_eq]
  exact hbound (min K L) H ε η hH hε hη hbasic hcutoff

/-- It suffices to impose the logarithmic condition at the small splitting
radius `L`. The full cutoff `K` remains unrestricted, but only its contribution
from directions of size at most `L` is estimated. -/
theorem trace_unresolved_small_weighted_bound_of_split_cutoff :
    ∃ D C : ℝ, 0 < D ∧ 0 < C ∧
      ∀ (K L H ε η : ℝ), 1 ≤ L → 1 ≤ H → 0 < ε → 0 < η →
      (2 + ε) * η ≤ traceCornerLowerConstant *
        Real.exp (-(2 * traceAxisLength) * H) →
      D * Real.log (2 * L) ≤ H →
      (∑ d ∈ (primitiveUnresolvedUpTo K H η K).filter (fun d ↦ intEuclidean d ≤ L),
        traceUnresolvedArcLength d K H η / intEuclidean d) ≤ C / (H * Real.sqrt H) := by
  obtain ⟨D, C, hD, hC, hbound⟩ := trace_weighted_unresolved_bound
  refine ⟨D, C, hD, hC, ?_⟩
  intro K L H ε η _hL hH hε hη hbasic hcutoff
  rw [trace_unresolved_small_weighted_sum_eq]
  by_cases hsmall : min K L < 1
  · rw [primitiveUnresolvedUpTo_eq_empty_of_lt_one (min K L) H η (min K L) hsmall,
      Finset.sum_empty]
    exact div_nonneg hC.le (mul_nonneg (by linarith) (Real.sqrt_nonneg H))
  · have hmin : 1 ≤ min K L := le_of_not_gt hsmall
    have hlog : Real.log (2 * min K L) ≤ Real.log (2 * L) :=
      Real.log_le_log (by linarith) (mul_le_mul_of_nonneg_left (min_le_right K L) (by norm_num))
    exact hbound (min K L) H ε η hH hε hη hbasic
      ((mul_le_mul_of_nonneg_left hlog hD.le).trans hcutoff)

end Markov
