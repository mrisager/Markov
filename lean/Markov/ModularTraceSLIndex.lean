import Markov.ModularTraceIndex

/-! The actual special-linear lift has index twelve, distinct from the
projective index six. The additional factor is the proved two-element
central kernel, which meets the lift only in the identity. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

theorem modularInteger_center_card : Nat.card (Subgroup.center SL(2, ℤ)) = 2 := by
  apply Nat.card_eq_two_iff.mpr
  refine ⟨⟨1, (Subgroup.center _).one_mem⟩,
    ⟨-1, (modularInteger_mem_center_iff _).mpr (Or.inr rfl)⟩, ?_, ?_⟩
  · intro h
    have heq := congrArg (fun g : Subgroup.center SL(2, ℤ) => g.val 0 0) h
    norm_num at heq
  · ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (modularInteger_mem_center_iff g.val).mp g.property with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

theorem modularTraceSubgroup_inf_center :
    modularTraceSubgroup ⊓ Subgroup.center SL(2, ℤ) = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  change g = 1
  rcases (modularInteger_mem_center_iff g).mp hg.2 with h | h
  · exact h
  · exact (neg_one_not_mem_modularTraceSubgroup (h ▸ hg.1)).elim

theorem modularTraceSubgroup_relIndex_center :
    modularTraceSubgroup.relIndex (Subgroup.center SL(2, ℤ)) = 2 := by
  rw [← Subgroup.inf_relIndex_right modularTraceSubgroup (Subgroup.center SL(2, ℤ)),
    modularTraceSubgroup_inf_center, Subgroup.relIndex_bot_left,
    modularInteger_center_card]

theorem modularTraceSubgroup_sup_center_index :
    (modularTraceSubgroup ⊔ Subgroup.center SL(2, ℤ)).index = 6 := by
  have hi := Subgroup.index_comap_of_surjective modularTraceProjectiveSubgroup
    (QuotientGroup.mk'_surjective (Subgroup.center SL(2, ℤ)))
  change ((modularTraceSubgroup.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).comap
    (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).index =
      modularTraceProjectiveSubgroup.index at hi
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hi
  exact hi.trans modularTraceProjectiveSubgroup_index

/-- The exact index of the actual integral special-linear lift. -/
theorem modularTraceSubgroup_index : modularTraceSubgroup.index = 12 := by
  calc
    modularTraceSubgroup.index =
        modularTraceSubgroup.relIndex
          (modularTraceSubgroup ⊔ Subgroup.center SL(2, ℤ)) *
          (modularTraceSubgroup ⊔ Subgroup.center SL(2, ℤ)).index :=
      (Subgroup.relIndex_mul_index le_sup_left).symm
    _ = 12 := by
      rw [Subgroup.relIndex_sup_left, modularTraceSubgroup_relIndex_center,
        modularTraceSubgroup_sup_center_index]

theorem modularIntegralCommutator_index : (commutator SL(2, ℤ)).index = 12 := by
  rw [← modularTraceSubgroup_eq_commutator]
  exact modularTraceSubgroup_index

theorem paperTraceSubgroup_index : paperTraceSubgroup.index = 12 := by
  rw [paperTraceSubgroup_eq_modularTraceSubgroup]
  exact modularTraceSubgroup_index

end Markov
