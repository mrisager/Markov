import Markov.ModularProjectiveCenter
import Markov.ModularTraceCongruence

/-! Exact exclusions of the first five positive parabolic powers from
the actual projective trace subgroup. Both central signs are checked by
the already-certified finite congruence images; no index is assumed. -/

open scoped MatrixGroups
namespace Markov

theorem modularT_nat_pow_matrix (n : ℕ) :
    ((ModularGroup.T ^ n : SL(2, ℤ)) : IntMatrixTwo) = !![1, (n : ℤ); 0, 1] := by
  simpa only [zpow_natCast] using ModularGroup.coe_T_zpow (n : ℤ)

private theorem modularT_small_power_congruence_exclusion :
    ∀ n : Fin 6, 0 < n.val →
      (traceMatrixReduction 4 !![1, (n.val : ℤ); 0, 1] ∉ traceModFourImage ∨
        traceMatrixReduction 3 !![1, (n.val : ℤ); 0, 1] ∉ traceModThreeImage) ∧
      (traceMatrixReduction 4 (-!![1, (n.val : ℤ); 0, 1]) ∉ traceModFourImage ∨
        traceMatrixReduction 3 (-!![1, (n.val : ℤ); 0, 1]) ∉ traceModThreeImage) := by
  decide

theorem modularT_pow_not_mem_modularTraceSubgroup
    (n : ℕ) (hn : 0 < n) (hn6 : n < 6) :
    ModularGroup.T ^ n ∉ modularTraceSubgroup := by
  intro hmem
  have hfour := modularTraceSubgroup_reduction_four_mem _ hmem
  have hthree := modularTraceSubgroup_reduction_three_mem _ hmem
  rw [modularT_nat_pow_matrix] at hfour hthree
  rcases (modularT_small_power_congruence_exclusion ⟨n, hn6⟩ hn).1 with h | h
  · exact h hfour
  · exact h hthree

theorem modular_neg_T_pow_not_mem_modularTraceSubgroup
    (n : ℕ) (hn : 0 < n) (hn6 : n < 6) :
    -(ModularGroup.T ^ n) ∉ modularTraceSubgroup := by
  intro hmem
  have hfour := modularTraceSubgroup_reduction_four_mem _ hmem
  have hthree := modularTraceSubgroup_reduction_three_mem _ hmem
  simp only [Matrix.SpecialLinearGroup.coe_neg, modularT_nat_pow_matrix] at hfour hthree
  rcases (modularT_small_power_congruence_exclusion ⟨n, hn6⟩ hn).2 with h | h
  · exact h hfour
  · exact h hthree

theorem modularT_projectivization_pow_not_mem_trace
    (n : ℕ) (hn : 0 < n) (hn6 : n < 6) :
    modularIntegralProjectivization (ModularGroup.T ^ n) ∉
      modularTraceProjectiveSubgroup := by
  intro hmem
  rcases (modularIntegralProjectivization_mem_trace_iff _).mp hmem with h | h
  · exact modularT_pow_not_mem_modularTraceSubgroup n hn hn6 h
  · exact modular_neg_T_pow_not_mem_modularTraceSubgroup n hn hn6 h

theorem modularT_projective_pow_not_mem_trace
    (n : ℕ) (hn : 0 < n) (hn6 : n < 6) :
    modularIntegralProjectivization ModularGroup.T ^ n ∉
      modularTraceProjectiveSubgroup := by
  simpa only [map_pow] using modularT_projectivization_pow_not_mem_trace n hn hn6

end Markov
