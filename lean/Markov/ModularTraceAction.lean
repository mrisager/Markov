import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Topology.Algebra.ConstMulAction

/-! The actual integral modular action preserves the hyperbolic metric.
Restriction to any concrete subgroup therefore remains isometric and
continuous. No freeness or proper-discontinuity assertion is made here. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

theorem modularInteger_smul_eq_real (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    g • z = (g : SL(2, ℝ)) • z := by
  apply UpperHalfPlane.ext
  rfl

theorem modularInteger_isometry (g : SL(2, ℤ)) :
    Isometry (fun z : UpperHalfPlane => g • z) := by
  simpa only [modularInteger_smul_eq_real] using
    isometry_smul UpperHalfPlane (g : SL(2, ℝ))

instance modularInteger_isIsometricSMul : IsIsometricSMul SL(2, ℤ) UpperHalfPlane :=
  ⟨modularInteger_isometry⟩

theorem modularSubgroup_isometry (Γ : Subgroup SL(2, ℤ)) (g : Γ) :
    Isometry (fun z : UpperHalfPlane => g • z) :=
  modularInteger_isometry g.val

instance modularSubgroup_isIsometricSMul (Γ : Subgroup SL(2, ℤ)) :
    IsIsometricSMul Γ UpperHalfPlane := ⟨modularSubgroup_isometry Γ⟩

theorem modularSubgroup_dist_invariant (Γ : Subgroup SL(2, ℤ)) (g : Γ)
    (z w : UpperHalfPlane) : dist (g • z) (g • w) = dist z w :=
  (modularSubgroup_isometry Γ g).dist_eq z w

theorem modularSubgroup_smul_continuous (Γ : Subgroup SL(2, ℤ)) (g : Γ) :
    Continuous (fun z : UpperHalfPlane => g • z) :=
  (modularSubgroup_isometry Γ g).continuous

/-- The subgroup action is the actual fractional-linear modular action. -/
theorem modularSubgroup_smul_complex (Γ : Subgroup SL(2, ℤ)) (g : Γ) (z : UpperHalfPlane) :
    ((g • z : UpperHalfPlane) : ℂ) =
      (((g.val 0 0 : ℂ) * (z : ℂ) + (g.val 0 1 : ℂ)) /
        ((g.val 1 0 : ℂ) * (z : ℂ) + (g.val 1 1 : ℂ))) :=
  UpperHalfPlane.coe_specialLinearGroup_apply g.val z

end Markov
