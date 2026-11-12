import Markov.ModularTraceCovering
import Mathlib.Topology.Homotopy.Lifting

/-! The actual fibre/deck-group correspondence and equivariance of
monodromy for the constructed modular covering. No surface classification,
homology identification or geometric norm agreement is assumed. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

abbrev ModularTraceFibre (z : UpperHalfPlane) :=
  modularTraceQuotientMk ⁻¹' {modularTraceQuotientMk z}

def modularTraceFibreOrbit (z : UpperHalfPlane) (g : modularTraceSubgroup) :
    ModularTraceFibre z :=
  ⟨g • z, modularTraceQuotientMk_smul g z⟩

theorem modularTraceFibreOrbit_injective (z : UpperHalfPlane) :
    Function.Injective (modularTraceFibreOrbit z) := by
  intro g h heq
  have heq' : g • z = h • z := congrArg Subtype.val heq
  have hfix : (h⁻¹ * g) • z = z := by
    rw [mul_smul, heq', inv_smul_smul]
  have hh : h⁻¹ * g = 1 := by
    apply Subtype.ext
    exact modularTraceSubgroup_eq_one_of_fixed_point _ (h⁻¹ * g).property z hfix
  exact (inv_mul_eq_one.mp hh).symm

theorem modularTraceFibreOrbit_surjective (z : UpperHalfPlane) :
    Function.Surjective (modularTraceFibreOrbit z) := by
  intro e
  obtain ⟨g, hg⟩ := (modularTraceQuotientMk_eq_iff e.val z).mp e.property
  exact ⟨g, Subtype.ext hg⟩

/-- This is the fibre of the actual quotient projection, with the actual
acting group; bijectivity uses orbit coverage and the proved free action. -/
def modularTraceFibreEquiv (z : UpperHalfPlane) :
    modularTraceSubgroup ≃ ModularTraceFibre z :=
  Equiv.ofBijective (modularTraceFibreOrbit z)
    ⟨modularTraceFibreOrbit_injective z, modularTraceFibreOrbit_surjective z⟩

@[simp] theorem modularTraceFibreEquiv_apply (z : UpperHalfPlane)
    (g : modularTraceSubgroup) : (modularTraceFibreEquiv z g).val = g • z := rfl

def modularTraceFibreTranslate (z : UpperHalfPlane) (g : modularTraceSubgroup)
    (e : ModularTraceFibre z) : ModularTraceFibre z :=
  ⟨g • e.val, (modularTraceQuotientMk_smul g e.val).trans e.property⟩

@[simp] theorem modularTraceFibreTranslate_val (z : UpperHalfPlane)
    (g : modularTraceSubgroup) (e : ModularTraceFibre z) :
    (modularTraceFibreTranslate z g e).val = g • e.val := rfl

theorem modularTraceFibreEquiv_mul (z : UpperHalfPlane)
    (g h : modularTraceSubgroup) :
    modularTraceFibreEquiv z (g * h) =
      modularTraceFibreTranslate z g (modularTraceFibreEquiv z h) :=
  Subtype.ext (mul_smul g h z)

/-- Actual monodromy commutes with the actual subgroup deck translations.
This is proved from unique path lifting, not assumed as a group action field. -/
theorem modularTraceMonodromy_translate (z : UpperHalfPlane)
    (g : modularTraceSubgroup)
    (c : Path.Homotopic.Quotient (modularTraceQuotientMk z) (modularTraceQuotientMk z))
    (e : ModularTraceFibre z) :
    modularTraceQuotientMk_isCoveringMap.monodromy c (modularTraceFibreTranslate z g e) =
      modularTraceFibreTranslate z g (modularTraceQuotientMk_isCoveringMap.monodromy c e) := by
  obtain ⟨γ⟩ := c
  apply Subtype.ext
  let cov := modularTraceQuotientMk_isCoveringMap
  let L := cov.liftPath γ e.val (γ.source.trans e.property.symm)
  have hl : (fun t => g • L t) =
      cov.liftPath γ (g • e.val)
        (γ.source.trans ((modularTraceQuotientMk_smul g e.val).trans e.property).symm) := by
    apply (cov.eq_liftPath_iff _).mpr
    refine ⟨(modularTraceSubgroup_isometry g).continuous.comp L.continuous, ?_, ?_⟩
    · funext t
      change modularTraceQuotientMk (g • L t) = γ t
      rw [modularTraceQuotientMk_smul]
      exact congr_fun (cov.liftPath_lifts γ e.val _) t
    · change g • L 0 = g • e.val
      rw [show L 0 = e.val from cov.liftPath_zero γ e.val _]
  exact (congr_fun hl 1).symm

end Markov
