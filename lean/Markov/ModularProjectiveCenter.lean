import Markov.ModularTraceCongruence

/-! The exact central sign ambiguity of the integral projective modular
group, distinguished from membership in the generated special-linear lift. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

theorem modularInteger_mem_center_iff (g : SL(2, ℤ)) :
    g ∈ Subgroup.center SL(2, ℤ) ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro hg
    obtain ⟨r, hr, heq⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
    have hs : r ^ 2 = 1 := by simpa using hr
    rcases sq_eq_one_iff.mp hs with h | h
    · left
      apply Subtype.ext
      simpa [h] using heq.symm
    · right
      apply Subtype.ext
      simpa [h] using heq.symm
  · rintro (rfl | rfl)
    · exact (Subgroup.center _).one_mem
    · apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
      exact ⟨-1, by decide, by decide⟩

/-- The actual projectivization, with its full central kernel. -/
def modularIntegralProjectivization : SL(2, ℤ) →* PSL(2, ℤ) :=
  QuotientGroup.mk' (Subgroup.center SL(2, ℤ))

theorem modularIntegralProjectivization_eq_iff (g h : SL(2, ℤ)) :
    modularIntegralProjectivization g = modularIntegralProjectivization h ↔
      g = h ∨ g = -h := by
  constructor
  · intro heq
    obtain ⟨z, hz, hgz⟩ := (QuotientGroup.mk'_eq_mk' (Subgroup.center SL(2, ℤ))).mp heq
    rcases (modularInteger_mem_center_iff z).mp hz with hz | hz
    · left
      simpa [hz] using hgz
    · right
      have hh : -g = h := by simpa [hz] using hgz
      exact (neg_eq_iff_eq_neg).mp hh
  · rintro (rfl | hneg)
    · rfl
    · apply (QuotientGroup.mk'_eq_mk' (Subgroup.center SL(2, ℤ))).mpr
      refine ⟨-1, (modularInteger_mem_center_iff _).mpr (Or.inr rfl), ?_⟩
      simp [hneg]

/-- Membership in the projective image permits both central signs; it
must not be silently identified with membership in the SL lift. -/
theorem modularIntegralProjectivization_mem_trace_iff (g : SL(2, ℤ)) :
    modularIntegralProjectivization g ∈ modularTraceProjectiveSubgroup ↔
      g ∈ modularTraceSubgroup ∨ -g ∈ modularTraceSubgroup := by
  constructor
  · rintro ⟨h, hh, heq⟩
    rcases (modularIntegralProjectivization_eq_iff h g).mp heq with he | he
    · exact Or.inl (he ▸ hh)
    · exact Or.inr (he ▸ hh)
  · rintro (hg | hg)
    · exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    · exact Subgroup.mem_map.mpr ⟨-g, hg,
        (modularIntegralProjectivization_eq_iff (-g) g).mpr (Or.inr rfl)⟩

end Markov
