import Markov.SupportLimit
import Markov.TraceArcs

/-! Actual Euclidean normal directions and endpoint closure for the interior
of a two-ray cone. The set below is defined from all norming functionals of
`a + t • b`, with `0 < t < ε`; its endpoint membership is a conclusion.
This module does not identify this cone section with a global cutoff normal
arc. The coordinate basis and the independent pair of approaching rays may
be chosen separately. -/

noncomputable section
open Set Filter
open scoped Topology

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluations on a basis, equipped with the actual Euclidean norm. -/
def euclideanDualCoordinates (C : Module.Basis (Fin 2) ℝ E)
    (f : StrongDual ℝ E) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i => f (C i))

@[simp] theorem euclideanDualCoordinates_apply (C : Module.Basis (Fin 2) ℝ E)
    (f : StrongDual ℝ E) (i : Fin 2) :
    euclideanDualCoordinates C f i = f (C i) := rfl

/-- These are exactly the existing dual coordinates, with Euclidean rather
than product maximum norm. -/
theorem euclideanDualCoordinates_pair (C : Module.Basis (Fin 2) ℝ E)
    (f : StrongDual ℝ E) :
    (euclideanDualCoordinates C f 0, euclideanDualCoordinates C f 1) =
      dualCoordinates C f := rfl

theorem continuous_euclideanDualCoordinates (C : Module.Basis (Fin 2) ℝ E) :
    Continuous (euclideanDualCoordinates C) := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    (continuous_pi (fun i => (ContinuousLinearMap.apply ℝ ℝ (C i)).continuous))

theorem euclideanDualCoordinates_ne_zero (C : Module.Basis (Fin 2) ℝ E)
    (f : StrongDual ℝ E) (hf : f ≠ 0) : euclideanDualCoordinates C f ≠ 0 := by
  intro hzero
  apply hf
  have heq : f.toLinearMap = (0 : StrongDual ℝ E).toLinearMap := by
    apply C.ext
    intro i
    have hi := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x i) hzero
    simpa using hi
  ext x
  exact LinearMap.congr_fun heq x

theorem normingFunctional_ne_zero (a : E) (ha : a ≠ 0)
    (f : StrongDual ℝ E) (hf : f ∈ normingFunctionals a) : f ≠ 0 := by
  intro hzero
  apply ha
  apply norm_eq_zero.mp
  simpa [hzero] using hf.2.symm

theorem normingFunctional_basisLine_ne_zero (B : Module.Basis (Fin 2) ℝ E)
    (t : ℝ) (f : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals (B 0 + t • B 1)) : f ≠ 0 :=
  normingFunctional_ne_zero _ (basis_affineLine_ne_zero B t) f hf

/-- Passing to the point of the unit sphere on a nonzero ray preserves all
norming supports. -/
theorem normingFunctionals_normalize_eq (a : E) (ha : a ≠ 0) :
    normingFunctionals (NormedSpace.normalize a) = normingFunctionals a := by
  ext f
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    have he := hf.2
    rw [NormedSpace.norm_normalize ha, NormedSpace.normalize, map_smul, smul_eq_mul] at he
    have hmul := congrArg (fun x : ℝ => ‖a‖ * x) he
    simpa only [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha),
      one_mul, mul_one] using hmul
  · intro hf
    refine ⟨hf.1, ?_⟩
    rw [NormedSpace.norm_normalize ha]
    exact normingFunctional_normalized_eq_one a ha f hf

/-- The actual unit Euclidean covector normal determined by a support. -/
def normalizedEuclideanCovector (C : Module.Basis (Fin 2) ℝ E)
    (f : StrongDual ℝ E) : EuclideanSpace ℝ (Fin 2) :=
  NormedSpace.normalize (euclideanDualCoordinates C f)

theorem normalizedEuclideanCovector_continuousAt (C : Module.Basis (Fin 2) ℝ E)
    (f : StrongDual ℝ E) (hf : f ≠ 0) :
    ContinuousAt (normalizedEuclideanCovector C) f := by
  have hc := (continuous_euclideanDualCoordinates C).continuousAt (x := f)
  exact (hc.norm.inv₀ (norm_ne_zero_iff.mpr
    (euclideanDualCoordinates_ne_zero C f hf))).smul hc

theorem norm_normalizedEuclideanCovector (C : Module.Basis (Fin 2) ℝ E)
    (f : StrongDual ℝ E) (hf : f ≠ 0) :
    ‖normalizedEuclideanCovector C f‖ = 1 :=
  NormedSpace.norm_normalize (euclideanDualCoordinates_ne_zero C f hf)

theorem norm_normalizedEuclideanCovector_of_norming (C : Module.Basis (Fin 2) ℝ E)
    (a : E) (ha : a ≠ 0) (f : StrongDual ℝ E) (hf : f ∈ normingFunctionals a) :
    ‖normalizedEuclideanCovector C f‖ = 1 :=
  norm_normalizedEuclideanCovector C f (normingFunctional_ne_zero a ha f hf)

/-- All actual normal directions above the open, bounded cone parameter
interval. No closure assumption is included in this definition. -/
def interiorConeNormals (C : Module.Basis (Fin 2) ℝ E) (a b : E) (ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  normalizedEuclideanCovector C ''
    {f | ∃ t ∈ Set.Ioo (0 : ℝ) ε, f ∈ normingFunctionals (a + t • b)}

/-- Actual normals at the unit-sphere points of the bounded radial section. -/
def interiorRadialNormals (B C : Module.Basis (Fin 2) ℝ E) (ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  normalizedEuclideanCovector C ''
    {f | ∃ t ∈ Set.Ioo (0 : ℝ) ε, f ∈ normingFunctionals (radialBasisSection B t)}

theorem interiorRadialNormals_eq_interiorConeNormals
    (B C : Module.Basis (Fin 2) ℝ E) (ε : ℝ) :
    interiorRadialNormals B C ε = interiorConeNormals C (B 0) (B 1) ε := by
  simp only [interiorRadialNormals, interiorConeNormals, radialBasisSection,
    normingFunctionals_normalize_eq _ (basis_affineLine_ne_zero B _)]

/-- Arbitrary norming choices converge to the selected endpoint normal.
`B` certifies independence of the rays; `C` is any coordinate basis. -/
theorem normalizedNormingSupport_tendsto_selectedSupport
    (B C : Module.Basis (Fin 2) ℝ E) (f : ℝ → StrongDual ℝ E)
    (hf : ∀ t : ℝ, 0 < t → f t ∈ normingFunctionals (B 0 + t • B 1)) :
    Tendsto (fun t => normalizedEuclideanCovector C (f t))
      (𝓝[>] (0 : ℝ)) (𝓝 (normalizedEuclideanCovector C (selectedSupport B))) := by
  apply (normalizedEuclideanCovector_continuousAt C (selectedSupport B) ?_).tendsto.comp
    (normingSupport_tendsto_selectedSupport B f hf)
  exact normingFunctional_ne_zero (B 0) (B.ne_zero 0)
    (selectedSupport B) (selectedSupport_spec B).1

/-- The selected endpoint normal is in the closure of the actual normals
over every positive bounded interval of cone parameters. -/
theorem selectedSupport_normal_mem_closure_interiorConeNormals
    (B C : Module.Basis (Fin 2) ℝ E) (ε : ℝ) (hε : 0 < ε) :
    normalizedEuclideanCovector C (selectedSupport B) ∈
      closure (interiorConeNormals C (B 0) (B 1) ε) := by
  let f : ℝ → StrongDual ℝ E := fun t =>
    Classical.choose (normingFunctionals_nonempty (B 0 + t • B 1))
  have hf : ∀ t : ℝ, f t ∈ normingFunctionals (B 0 + t • B 1) :=
    fun t => Classical.choose_spec (normingFunctionals_nonempty (B 0 + t • B 1))
  apply mem_closure_of_tendsto
    (normalizedNormingSupport_tendsto_selectedSupport B C f (fun t _ => hf t))
  have hlt : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < ε :=
    (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with t ht htε
  exact ⟨f t, ⟨t, ⟨ht, htε⟩, hf t⟩, rfl⟩

/-- The same endpoint statement for independent integral rays, with their
nonzero determinant displayed explicitly. -/
theorem selectedSupportAt_normal_mem_closure_interiorConeNormals
    (B C : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ) (hdet : intDet u v ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    normalizedEuclideanCovector C (selectedSupportAt B u v) ∈
      closure (interiorConeNormals C (intVector B u) (intVector B v) ε) := by
  rw [selectedSupportAt, dif_pos hdet]
  simpa only [intPairBasis_zero, intPairBasis_one] using
    selectedSupport_normal_mem_closure_interiorConeNormals (intPairBasis B u v hdet) C ε hε

/-- The endpoint is approached by genuine normals of the unit-sphere
section, not merely normals of an unnormalized parameterization. -/
theorem selectedSupport_normal_mem_closure_interiorRadialNormals
    (B C : Module.Basis (Fin 2) ℝ E) (ε : ℝ) (hε : 0 < ε) :
    normalizedEuclideanCovector C (selectedSupport B) ∈
      closure (interiorRadialNormals B C ε) := by
  rw [interiorRadialNormals_eq_interiorConeNormals]
  exact selectedSupport_normal_mem_closure_interiorConeNormals B C ε hε

end Markov
