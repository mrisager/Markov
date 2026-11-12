import Markov.PrimitiveSimpleGeodesicLengthAgreement
import Markov.TraceNormTransfer
import Markov.TracePrimitiveRayPoisson

/-! The imported unconditional geometric primitive-agreement theorem supplies
the genuine geometric values before the intrinsic norm is chosen.

The norm is chosen from a proved unique extension of the independently
defined geometric primitive lengths. The trace gauge is a witness in the
existence proof after genuine agreement, not the definition of this norm. -/
noncomputable section
open Set
namespace Markov

/-- A genuine continuous norm extending only the ACTUAL geometric primitive
length datum. No trace value, class correspondence or agreement field occurs
in this definition. Nonprimitive values are determined by homogeneity. -/
def IsModularIntrinsicNormExtension
    (F : EuclideanSpace ℝ (Fin 2) → ℝ) : Prop :=
  Continuous F ∧
    (∀ a : ℝ, ∀ x, F (a • x) = |a| * F x) ∧
    (∀ x, 0 ≤ F x) ∧
    (∀ x, F x = 0 ↔ x = 0) ∧
    (∀ x y, F (x+y) ≤ F x + F y) ∧
    (∀ p : ℤ × ℤ, IsCoprime p.1 p.2 →
      F (euclideanIntDirection p) = modularSimpleGeodesicLengthInf p)

private theorem intrinsicExtension_traceGauge :
    IsModularIntrinsicNormExtension traceEuclideanGauge := by
  refine ⟨continuous_norm.comp traceEuclideanEquiv.symm.continuous,
    traceEuclideanGauge_smul,traceEuclideanGauge_nonneg,?_,
    traceEuclideanGauge_add_le,?_⟩
  · intro x
    change ‖traceEuclideanEquiv.symm x‖ = 0 ↔ x = 0
    rw [norm_eq_zero]
    constructor
    · intro hx
      have he := congrArg traceEuclideanEquiv hx
      simpa only [ContinuousLinearEquiv.apply_symm_apply,map_zero] using he
    · rintro rfl
      exact map_zero _
  · intro p hp
    rw [traceEuclideanGauge_intDirection,
      modularSimpleGeodesicLengthInf_eq_trace_norm p hp]

/-- Primitive geometric length agreement gives existence of the extension.
Uniqueness follows from its values on primitive lattice directions. -/
theorem existsUnique_modularIntrinsicNormExtension :
    ∃! F : EuclideanSpace ℝ (Fin 2) → ℝ, IsModularIntrinsicNormExtension F := by
  refine ⟨traceEuclideanGauge,intrinsicExtension_traceGauge,?_⟩
  intro F hF
  apply continuous_homogeneous_euclidean_ext_of_primitive F traceEuclideanGauge
    hF.1 intrinsicExtension_traceGauge.1 hF.2.1 intrinsicExtension_traceGauge.2.1
  intro p hp
  exact (hF.2.2.2.2.2 p hp).trans
    (intrinsicExtension_traceGauge.2.2.2.2.2 p hp).symm

/-- The intrinsic McShane–Rivin norm is chosen by its actual geometric
primitive-length characterization. Its definition does not name a trace gauge
or trace ball. Standard Euclidean norm and volume instances are unchanged. -/
def modularMcShaneRivinNorm : EuclideanSpace ℝ (Fin 2) → ℝ :=
  Classical.choose (existsUnique_modularIntrinsicNormExtension).exists

theorem modularMcShaneRivinNorm_spec :
    IsModularIntrinsicNormExtension modularMcShaneRivinNorm :=
  Classical.choose_spec (existsUnique_modularIntrinsicNormExtension).exists

theorem modularMcShaneRivinNorm_continuous : Continuous modularMcShaneRivinNorm :=
  modularMcShaneRivinNorm_spec.1

theorem modularMcShaneRivinNorm_smul (a : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    modularMcShaneRivinNorm (a • x) = |a| * modularMcShaneRivinNorm x :=
  modularMcShaneRivinNorm_spec.2.1 a x

theorem modularMcShaneRivinNorm_nonneg (x : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ modularMcShaneRivinNorm x :=
  modularMcShaneRivinNorm_spec.2.2.1 x

theorem modularMcShaneRivinNorm_eq_zero_iff (x : EuclideanSpace ℝ (Fin 2)) :
    modularMcShaneRivinNorm x = 0 ↔ x = 0 :=
  modularMcShaneRivinNorm_spec.2.2.2.1 x

@[simp] theorem modularMcShaneRivinNorm_zero : modularMcShaneRivinNorm 0 = 0 :=
  (modularMcShaneRivinNorm_eq_zero_iff 0).mpr rfl

theorem modularMcShaneRivinNorm_add_le (x y : EuclideanSpace ℝ (Fin 2)) :
    modularMcShaneRivinNorm (x+y) ≤ modularMcShaneRivinNorm x + modularMcShaneRivinNorm y :=
  modularMcShaneRivinNorm_spec.2.2.2.2.1 x y

/-- The defining primitive values are the actual geometric infima, without
reference to a chosen canonical trace representative. -/
theorem modularMcShaneRivinNorm_primitive
    (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    modularMcShaneRivinNorm (euclideanIntDirection p) = modularSimpleGeodesicLengthInf p :=
  modularMcShaneRivinNorm_spec.2.2.2.2.2 p hp

/-- Every admissible primitive geodesic period equals the value of the
intrinsic norm, by `modularSimpleGeodesicLengthSet_eq_singleton`. -/
theorem modularMcShaneRivinNorm_eq_actual_primitive_length
    (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) (L : ℝ)
    (hL : L ∈ modularSimpleGeodesicLengthSet p) :
    modularMcShaneRivinNorm (euclideanIntDirection p) = L := by
  have hlength : L = ‖intVector traceBasis p‖ := by
    rw [modularSimpleGeodesicLengthSet_eq_singleton p hp] at hL
    exact Set.mem_singleton_iff.mp hL
  rw [modularMcShaneRivinNorm_primitive p hp,
    modularSimpleGeodesicLengthInf_eq_trace_norm p hp,hlength]

/-- Integral multiples use homogeneity; no embedded-geodesic length-set
interpolation is imposed on nonprimitive classes. -/
theorem modularMcShaneRivinNorm_integer_multiple
    (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) (d : ℤ) :
    modularMcShaneRivinNorm (euclideanIntDirection (d • p)) =
      |(d : ℝ)| * modularSimpleGeodesicLengthInf p := by
  rw [euclideanIntDirection_zsmul,modularMcShaneRivinNorm_smul,
    modularMcShaneRivinNorm_primitive p hp]

/-- Genuine primitive agreement identifies the already intrinsically
defined norm with the constructed trace gauge everywhere by continuity. -/
theorem modularMcShaneRivinNorm_eq_traceEuclideanGauge :
    modularMcShaneRivinNorm = traceEuclideanGauge := by
  apply eq_traceEuclideanGauge_of_primitive_values modularMcShaneRivinNorm
    modularMcShaneRivinNorm_continuous modularMcShaneRivinNorm_smul
  intro p hp
  rw [modularMcShaneRivinNorm_primitive p hp,
    modularSimpleGeodesicLengthInf_eq_trace_norm p hp]

theorem modularMcShaneRivinNorm_primitive_trace_value
    (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    modularMcShaneRivinNorm (euclideanIntDirection p) = ‖intVector traceBasis p‖ := by
  rw [modularMcShaneRivinNorm_primitive p hp,
    modularSimpleGeodesicLengthInf_eq_trace_norm p hp]

end Markov
