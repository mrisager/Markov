import Markov.ModularTraceCyclicQuotient
import Markov.ModularTraceParabolicPowers
import Mathlib.GroupTheory.Index

/-! Exact index six of the actual projective modular commutator subgroup.
The upper bound comes from the actual modular generators and relations;
the lower bound uses the checked finite congruence images of its SL lift. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

theorem modularTraceProjectiveQuotientT_pow_ne_one
    (n : ℕ) (hn : 0 < n) (hn6 : n < 6) :
    modularTraceProjectiveQuotientT ^ n ≠ 1 := by
  intro heq
  have heq' : modularTraceProjectiveQuotientMap (ModularGroup.T ^ n) = 1 := by
    simpa only [map_pow, modularTraceProjectiveQuotientT] using heq
  have hmem : modularIntegralProjectivization (ModularGroup.T ^ n) ∈
      modularTraceProjectiveSubgroup := (QuotientGroup.eq_one_iff _).mp heq'
  exact modularT_projectivization_pow_not_mem_trace n hn hn6 hmem

/-- The parabolic generator has exactly order six in the actual quotient. -/
theorem modularTraceProjectiveQuotientT_orderOf :
    orderOf modularTraceProjectiveQuotientT = 6 := by
  apply (orderOf_eq_iff (by decide : 0 < 6)).mpr
  exact ⟨modularTraceProjectiveQuotientT_pow_six,
    fun n hn6 hn => modularTraceProjectiveQuotientT_pow_ne_one n hn hn6⟩

theorem modularTraceProjectiveQuotient_card :
    Nat.card ModularTraceProjectiveQuotient = 6 := by
  rw [← orderOf_eq_card_of_zpowers_eq_top
    modularTraceProjectiveQuotient_zpowers_T_eq_top,
    modularTraceProjectiveQuotientT_orderOf]

/-- This is the projective index; the central kernel must not be omitted
when comparing it with an index in the special-linear group. -/
theorem modularTraceProjectiveSubgroup_index :
    modularTraceProjectiveSubgroup.index = 6 := by
  rw [Subgroup.index_eq_card]
  exact modularTraceProjectiveQuotient_card

theorem modularProjectiveCommutator_index :
    (commutator PSL(2, ℤ)).index = 6 := by
  rw [← modularTraceProjectiveSubgroup_eq_commutator]
  exact modularTraceProjectiveSubgroup_index

end Markov
