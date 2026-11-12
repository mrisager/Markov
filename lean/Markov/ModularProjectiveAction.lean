import Markov.ModularTraceCommutator
import Markov.ModularProjectiveCenter
import Markov.ModularTraceCovering
import Mathlib.Algebra.Group.Action.End

/-! The actual projective modular action and equality of the paper
commutator orbits with the already constructed covering quotient orbits.
The central kernel acts trivially; it is not discarded by an assumption. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

def modularProjectiveActionHom : PSL(2, ℤ) →* Function.End UpperHalfPlane :=
  QuotientGroup.lift (Subgroup.center SL(2, ℤ))
    (MulAction.toEndHom : SL(2, ℤ) →* Function.End UpperHalfPlane) (by
      intro g hg
      funext z
      change g • z = z
      rcases (modularInteger_mem_center_iff g).mp hg with rfl | rfl
      · exact one_smul _ _
      · simpa only [ModularGroup.SL_neg_smul] using (one_smul SL(2, ℤ) z))

instance modularProjective_mulAction : MulAction PSL(2, ℤ) UpperHalfPlane :=
  MulAction.ofEndHom modularProjectiveActionHom

@[simp] theorem modularProjectivization_smul (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    modularIntegralProjectivization g • z = g • z := rfl

theorem modularProjective_isometry (g : PSL(2, ℤ)) :
    Isometry (fun z : UpperHalfPlane => g • z) := by
  induction g using QuotientGroup.induction_on with
  | H g => exact modularInteger_isometry g

/-- The two actual subgroup actions give precisely the same orbit relation. -/
theorem modularTraceProjective_orbit_iff (z w : UpperHalfPlane) :
    (∃ g : modularTraceProjectiveSubgroup, g • w = z) ↔
      ∃ g : modularTraceSubgroup, g • w = z := by
  constructor
  · rintro ⟨⟨g, hg⟩, hact⟩
    obtain ⟨a, ha, rfl⟩ := hg
    exact ⟨⟨a, ha⟩, hact⟩
  · rintro ⟨g, hact⟩
    refine ⟨⟨modularIntegralProjectivization g.val, ?_⟩, hact⟩
    exact Subgroup.mem_map.mpr ⟨g.val, g.property, rfl⟩

/-- Equality in the existing actual quotient is equality of paper
projective commutator orbits, with the proved central-sign action. -/
theorem modularTraceQuotientMk_eq_iff_projective_commutator
    (z w : UpperHalfPlane) :
    modularTraceQuotientMk z = modularTraceQuotientMk w ↔
      ∃ g : commutator PSL(2, ℤ), g • w = z := by
  rw [modularTraceQuotientMk_eq_iff,
    ← modularTraceProjective_orbit_iff,
    modularTraceProjectiveSubgroup_eq_commutator]

end Markov
