import Markov.PaperModularCommutators
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.GroupTheory.Commutator.Basic

/-! Commutator identification from actual modular generators. No index
calculation or geometric quotient identification is used. -/

noncomputable section
open scoped MatrixGroups
open ModularGroup
namespace Markov

/-- Killing the actual modular generator commutator makes any normal
quotient of the integral special-linear group commutative. -/
theorem modularQuotient_commutative_of_commutatorST_mem
    (Γ : Subgroup SL(2, ℤ)) [Γ.Normal] (hST : ⁅S, T⁆ ∈ Γ) :
    Std.Commutative (· * · : SL(2, ℤ) ⧸ Γ → _ → _) := by
  let f := QuotientGroup.mk' Γ
  have hst : Commute (f S) (f T) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr hST
  have hgen : Subgroup.closure {f S, f T} = ⊤ := by
    rw [← Set.image_pair, ← MonoidHom.map_closure,
      SpecialLinearGroup.SL2Z_generators, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective Γ
  have hcomm : ∀ x ∈ ({f S, f T} : Set (SL(2, ℤ) ⧸ Γ)),
      ∀ y ∈ ({f S, f T} : Set (SL(2, ℤ) ⧸ Γ)), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hst.eq
    · exact hst.eq.symm
    · rfl
  letI : CommGroup (Subgroup.closure {f S, f T}) :=
    Subgroup.closureCommGroupOfComm hcomm
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ Subgroup.closure {f S, f T} := by rw [hgen]; trivial
  have hy : y ∈ Subgroup.closure {f S, f T} := by rw [hgen]; trivial
  exact congrArg Subtype.val
    (mul_comm (⟨x, hx⟩ : Subgroup.closure {f S, f T}) ⟨y, hy⟩)

/-- Surjective projectivization carries the full special-linear
commutator onto the full projective commutator. -/
theorem modular_commutator_map_projectivization :
    (commutator SL(2, ℤ)).map
      (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) = commutator PSL(2, ℤ) := by
  have hr : (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))).range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective (Subgroup.center SL(2, ℤ))
  rw [map_commutator_eq, hr]
  rfl

theorem modularTraceSubgroup_le_commutator :
    modularTraceSubgroup ≤ commutator SL(2, ℤ) := by
  rw [← paperTraceSubgroup_eq_modularTraceSubgroup]
  apply (paperTraceSubgroup_le_iff _).mpr
  constructor
  · rw [paperGeneratorASL_eq_commutator]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · rw [paperGeneratorBSL_eq_commutator]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The actual generated subgroup has a commutative group quotient. -/
theorem modularTraceGroupQuotient_commutative :
    Std.Commutative (· * · : SL(2, ℤ) ⧸ modularTraceSubgroup → _ → _) := by
  apply modularQuotient_commutative_of_commutatorST_mem
  rw [← paperGeneratorASL_eq_commutator,
    ← paperTraceSubgroup_eq_modularTraceSubgroup]
  exact paperGeneratorASL_mem_paperTraceSubgroup

theorem commutator_le_modularTraceSubgroup :
    commutator SL(2, ℤ) ≤ modularTraceSubgroup :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
    modularTraceGroupQuotient_commutative

/-- Exact identification in the actual integral special-linear group. -/
theorem modularTraceSubgroup_eq_commutator :
    modularTraceSubgroup = commutator SL(2, ℤ) :=
  le_antisymm modularTraceSubgroup_le_commutator commutator_le_modularTraceSubgroup

theorem paperTraceSubgroup_eq_commutator :
    paperTraceSubgroup = commutator SL(2, ℤ) :=
  paperTraceSubgroup_eq_modularTraceSubgroup.trans modularTraceSubgroup_eq_commutator

/-- The concrete projective image is the paper's projective modular
commutator subgroup; no index value enters this proof. -/
theorem modularTraceProjectiveSubgroup_eq_commutator :
    modularTraceProjectiveSubgroup = commutator PSL(2, ℤ) := by
  unfold modularTraceProjectiveSubgroup
  rw [modularTraceSubgroup_eq_commutator, modular_commutator_map_projectivization]

instance modularTraceProjectiveSubgroup_normal : modularTraceProjectiveSubgroup.Normal := by
  rw [modularTraceProjectiveSubgroup_eq_commutator]
  infer_instance

end Markov
