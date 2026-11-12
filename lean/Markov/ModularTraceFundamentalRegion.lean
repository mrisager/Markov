import Markov.ModularTraceIndex
import Markov.ModularProjectiveAction
import Mathlib.NumberTheory.Modular

/-! Six actual standard modular cells cover the trace quotient. Their
open cells are separated under the actual trace subgroup action. Central
signs are retained in the group calculation and removed only by their
proved trivial action. No polygon or punctured-torus identification is asserted. -/

noncomputable section
open scoped MatrixGroups
open Set
namespace Markov

theorem modularTraceQuotient_T_pow_representative (g : SL(2, ℤ)) :
    ∃ r : Fin 6, modularTraceProjectiveQuotientT ^ r.val =
      modularTraceProjectiveQuotientMap g := by
  classical
  have hmem : modularTraceProjectiveQuotientMap g ∈
      Subgroup.zpowers modularTraceProjectiveQuotientT := by
    rw [modularTraceProjectiveQuotient_zpowers_T_eq_top]
    trivial
  rw [mem_zpowers_iff_mem_range_orderOf, modularTraceProjectiveQuotientT_orderOf] at hmem
  obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hmem
  exact ⟨⟨n, Finset.mem_range.mp hn⟩, heq⟩

/-- The six representatives are representatives for the action, with
the full central sign ambiguity accounted for in the special-linear lift. -/
theorem modularTrace_action_coset_decomposition (g : SL(2, ℤ)) :
    ∃ γ : modularTraceSubgroup, ∃ r : Fin 6,
      ∀ z : UpperHalfPlane, g • z = γ • (ModularGroup.T ^ r.val • z) := by
  obtain ⟨r, hr⟩ := modularTraceQuotient_T_pow_representative g
  let a : SL(2, ℤ) := g * (ModularGroup.T ^ r.val)⁻¹
  have hqa : modularTraceProjectiveQuotientMap a = 1 := by
    dsimp only [a]
    rw [map_mul, map_inv, map_pow, ← hr]
    exact mul_inv_cancel _
  have hmem : modularIntegralProjectivization a ∈ modularTraceProjectiveSubgroup :=
    (QuotientGroup.eq_one_iff _).mp hqa
  rcases (modularIntegralProjectivization_mem_trace_iff a).mp hmem with ha | ha
  · refine ⟨⟨a, ha⟩, r, ?_⟩
    intro z
    change g • z = (g * (ModularGroup.T ^ r.val)⁻¹) • (ModularGroup.T ^ r.val • z)
    simp only [mul_smul, inv_smul_smul]
  · refine ⟨⟨-a, ha⟩, r, ?_⟩
    intro z
    change g • z = (-a) • (ModularGroup.T ^ r.val • z)
    rw [ModularGroup.SL_neg_smul]
    change g • z = (g * (ModularGroup.T ^ r.val)⁻¹) • (ModularGroup.T ^ r.val • z)
    simp only [mul_smul, inv_smul_smul]

theorem modularTrace_six_fd_coverage (z : UpperHalfPlane) :
    ∃ γ : modularTraceSubgroup, ∃ r : Fin 6, ∃ w : UpperHalfPlane,
      w ∈ ModularGroup.fd ∧ z = γ • (ModularGroup.T ^ r.val • w) := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  obtain ⟨γ, r, hgr⟩ := modularTrace_action_coset_decomposition g⁻¹
  refine ⟨γ, r, g • z, hg, ?_⟩
  simpa only [inv_smul_smul] using hgr (g • z)

def modularTraceClosedCell (r : Fin 6) : Set UpperHalfPlane :=
  (fun z : UpperHalfPlane => ModularGroup.T ^ r.val • z) '' ModularGroup.fd

def modularTraceOpenCell (r : Fin 6) : Set UpperHalfPlane :=
  (fun z : UpperHalfPlane => ModularGroup.T ^ r.val • z) '' ModularGroup.fdo

def modularTraceSixRegion : Set UpperHalfPlane := ⋃ r : Fin 6, modularTraceClosedCell r

/-- The union of the six open standard cells; no equality with the
topological interior of the closed union is part of this definition. -/
def modularTraceSixOpenRegion : Set UpperHalfPlane := ⋃ r : Fin 6, modularTraceOpenCell r

theorem modularStandardClosedCell_isClosed : IsClosed ModularGroup.fd := by
  exact (isClosed_le continuous_const
    (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)).inter
    (isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const)

theorem modularStandardOpenCell_isOpen : IsOpen ModularGroup.fdo := by
  exact (isOpen_lt continuous_const
    (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)).inter
    (isOpen_lt (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const)

theorem modularTraceClosedCell_isClosed (r : Fin 6) : IsClosed (modularTraceClosedCell r) :=
  isClosedMap_smul (ModularGroup.T ^ r.val) _ modularStandardClosedCell_isClosed

theorem modularTraceOpenCell_isOpen (r : Fin 6) : IsOpen (modularTraceOpenCell r) :=
  isOpenMap_smul (ModularGroup.T ^ r.val) _ modularStandardOpenCell_isOpen

theorem modularTraceSixRegion_isClosed : IsClosed modularTraceSixRegion :=
  isClosed_iUnion_of_finite modularTraceClosedCell_isClosed

theorem modularTraceSixOpenRegion_isOpen : IsOpen modularTraceSixOpenRegion :=
  isOpen_iUnion modularTraceOpenCell_isOpen

theorem modularTraceOpenCell_subset_closedCell (r : Fin 6) :
    modularTraceOpenCell r ⊆ modularTraceClosedCell r := by
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z, ⟨hz.1.le, hz.2.le⟩, rfl⟩

theorem modularTraceSixOpenRegion_subset_sixRegion :
    modularTraceSixOpenRegion ⊆ modularTraceSixRegion :=
  iUnion_mono modularTraceOpenCell_subset_closedCell

theorem modularTraceSixRegion_coverage (z : UpperHalfPlane) :
    ∃ γ : modularTraceSubgroup, γ • z ∈ modularTraceSixRegion := by
  obtain ⟨γ, r, w, hw, hz⟩ := modularTrace_six_fd_coverage z
  refine ⟨γ⁻¹, ?_⟩
  rw [hz, inv_smul_smul]
  exact mem_iUnion.mpr ⟨r, ⟨w, hw, rfl⟩⟩

theorem modularTraceSixRegion_smul_iUnion_eq_univ :
    (⋃ γ : modularTraceSubgroup, (fun z : UpperHalfPlane => γ • z) ''
      modularTraceSixRegion) = univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨γ, r, w, hw, hz⟩ := modularTrace_six_fd_coverage z
  exact mem_iUnion.mpr ⟨γ, ⟨ModularGroup.T ^ r.val • w,
    mem_iUnion.mpr ⟨r, ⟨w, hw, rfl⟩⟩, hz.symm⟩⟩

theorem modularTraceQuotient_fd_representative (x : ModularTraceQuotient) :
    ∃ r : Fin 6, ∃ w : UpperHalfPlane, w ∈ ModularGroup.fd ∧
      modularTraceQuotientMk (ModularGroup.T ^ r.val • w) = x := by
  obtain ⟨z, rfl⟩ := modularTraceQuotientMk_surjective x
  obtain ⟨γ, r, w, hw, hz⟩ := modularTrace_six_fd_coverage z
  refine ⟨r, w, hw, ?_⟩
  rw [hz, modularTraceQuotientMk_smul]

/-- In the open full modular cell, the only possible returning integral
matrices are the two central scalars. -/
theorem modularInteger_eq_one_or_neg_one_of_mem_fdo_smul_mem_fdo
    (g : SL(2, ℤ)) (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fdo)
    (hgz : g • z ∈ ModularGroup.fdo) : g = 1 ∨ g = -1 := by
  have hc := ModularGroup.c_eq_zero hz hgz
  have hfix := (ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo hz hgz).symm
  let gr : SL(2, ℝ) := g
  have hfix' : gr • z = z := by
    rw [← modularInteger_smul_eq_real]
    exact hfix
  have hc' : gr 1 0 = 0 := by
    change ((g 1 0 : ℤ) : ℝ) = 0
    exact_mod_cast hc
  have htr : (gr : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 = 4 := by
    have hi := sl_fixed_point_trace_identity gr z hfix'
    simpa only [hc', zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, sub_zero] using hi
  rcases sl_fixed_point_eq_one_or_neg_one_of_trace_sq_eq_four gr z hfix' htr with h | h
  · left
    apply modularInteger_real_injective
    simpa [gr] using h
  · right
    apply modularInteger_real_injective
    simpa [gr] using h

/-- Open standard cells in the six representatives have distinct trace
orbits, and their individual points have no nontrivial identification. -/
theorem modularTrace_openCell_orbit_separation
    (γ : modularTraceSubgroup) (r s : Fin 6) (z w : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fdo) (hw : w ∈ ModularGroup.fdo)
    (heq : γ • (ModularGroup.T ^ r.val • z) = ModularGroup.T ^ s.val • w) :
    γ = 1 ∧ r = s ∧ z = w := by
  have heq' : γ.val • (ModularGroup.T ^ r.val • z) = ModularGroup.T ^ s.val • w := heq
  let h : SL(2, ℤ) := (ModularGroup.T ^ s.val)⁻¹ * γ.val * ModularGroup.T ^ r.val
  have hact : h • z = w := by
    dsimp only [h]
    rw [mul_smul, mul_smul]
    rw [heq', inv_smul_smul]
  have hmem : h • z ∈ ModularGroup.fdo := hact.symm ▸ hw
  have hzw : z = w :=
    (ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo hz hmem).trans hact
  have hqh : modularTraceProjectiveQuotientMap h = 1 := by
    rcases modularInteger_eq_one_or_neg_one_of_mem_fdo_smul_mem_fdo h z hz hmem with hh | hh
    · rw [hh, map_one]
    · rw [hh, modularTraceProjectiveQuotientMap_neg_one]
  have hqγ : modularTraceProjectiveQuotientMap γ.val = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.mem_map.mpr ⟨γ.val, γ.property, rfl⟩
  have hrel : (modularTraceProjectiveQuotientT ^ s.val)⁻¹ *
      modularTraceProjectiveQuotientT ^ r.val = 1 := by
    simpa only [h, map_mul, map_inv, map_pow, hqγ, mul_one,
      modularTraceProjectiveQuotientT] using hqh
  have hp : modularTraceProjectiveQuotientT ^ s.val =
      modularTraceProjectiveQuotientT ^ r.val := inv_mul_eq_one.mp hrel
  have hmod : s.val % 6 = r.val % 6 := by
    simpa only [modularTraceProjectiveQuotientT_orderOf] using pow_inj_mod.mp hp
  have hrs : r = s := Fin.ext (by
    simpa only [Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt r.isLt] using hmod.symm)
  subst s
  subst w
  have hγ := modularTraceSubgroup_eq_one_of_fixed_point γ.val γ.property
    (ModularGroup.T ^ r.val • z) heq
  exact ⟨Subtype.ext hγ, rfl, rfl⟩

theorem modularTraceQuotientMk_openCell_eq_iff
    (r s : Fin 6) (z w : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fdo) (hw : w ∈ ModularGroup.fdo) :
    modularTraceQuotientMk (ModularGroup.T ^ r.val • z) =
      modularTraceQuotientMk (ModularGroup.T ^ s.val • w) ↔ r = s ∧ z = w := by
  constructor
  · intro heq
    obtain ⟨γ, hγ⟩ := (modularTraceQuotientMk_eq_iff _ _).mp heq.symm
    exact (modularTrace_openCell_orbit_separation γ r s z w hz hw hγ).2
  · rintro ⟨rfl, rfl⟩
    rfl

theorem modularTraceQuotientMk_injOn_sixOpenRegion :
    InjOn modularTraceQuotientMk modularTraceSixOpenRegion := by
  rintro x hx y hy heq
  obtain ⟨r, z, hz, rfl⟩ := mem_iUnion.mp hx
  obtain ⟨s, w, hw, rfl⟩ := mem_iUnion.mp hy
  obtain ⟨hrs, hzw⟩ := (modularTraceQuotientMk_openCell_eq_iff r s z w hz hw).mp heq
  rw [hrs, hzw]

theorem modularTraceOpenCell_projected_pairwise_disjoint :
    Pairwise fun r s : Fin 6 => Disjoint
      (modularTraceQuotientMk '' modularTraceOpenCell r)
      (modularTraceQuotientMk '' modularTraceOpenCell s) := by
  intro r s hrs
  apply disjoint_left.mpr
  rintro x ⟨y, hy, hyx⟩ ⟨y', hy', hyx'⟩
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨w, hw, rfl⟩ := hy'
  exact hrs ((modularTraceQuotientMk_openCell_eq_iff r s z w hz hw).mp
    (hyx.trans hyx'.symm)).1

end Markov
