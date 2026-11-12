import Markov.SupportLimit
import Markov.SupportAngleEnvelope

/-! The actual selected support along a basis affine line. The shear basis
has first vector `B 0 + t • B 1` and second vector `B 1`. Its selected
support is right-continuous in operator norm, as a consequence of the
one-sided support limit theorem rather than a continuity assumption.
The corresponding support angle is right-continuous wherever its limit
lies in the proved positive-sum angle branch. No global cyclic lift or
quantitative turn bound is constructed here. -/

noncomputable section
open Set Filter
open scoped Topology

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The linear shear fixing the second basis vector. Its inverse uses
the opposite shear parameter. -/
def affineBasisShear (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) : E ≃ₗ[ℝ] E where
  toLinearMap := LinearMap.id + (B.coord 0).smulRight (t • B 1)
  invFun := fun x => x + (B.coord 0 x) • ((-t) • B 1)
  left_inv := by
    intro x
    change (x + (B.coord 0 x) • (t • B 1)) +
      (B.coord 0 (x + (B.coord 0 x) • (t • B 1))) • ((-t) • B 1) = x
    have hcoord : B.coord 0 (x + (B.coord 0 x) • (t • B 1)) = B.coord 0 x := by
      simp
    rw [hcoord]
    module
  right_inv := by
    intro x
    change (x + (B.coord 0 x) • ((-t) • B 1)) +
      (B.coord 0 (x + (B.coord 0 x) • ((-t) • B 1))) • (t • B 1) = x
    have hcoord : B.coord 0 (x + (B.coord 0 x) • ((-t) • B 1)) = B.coord 0 x := by
      simp
    rw [hcoord]
    module

theorem affineBasisShear_apply (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) (x : E) :
    affineBasisShear B t x = x + (B.coord 0 x) • (t • B 1) := rfl

/-- The actual basis adapted to the affine point and its increasing
parameter direction. -/
def affinePairBasis (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) :
    Module.Basis (Fin 2) ℝ E := B.map (affineBasisShear B t)

@[simp] theorem affinePairBasis_zero (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) :
    affinePairBasis B t 0 = B 0 + t • B 1 := by
  simp [affinePairBasis, Module.Basis.map_apply, affineBasisShear_apply]

@[simp] theorem affinePairBasis_one (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) :
    affinePairBasis B t 1 = B 1 := by
  simp [affinePairBasis, Module.Basis.map_apply, affineBasisShear_apply]

/-- The support at the affine point selected by increasing parameter. -/
def selectedAffineSupport (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) : StrongDual ℝ E :=
  selectedSupport (affinePairBasis B t)

theorem selectedAffineSupport_spec (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) :
    IsSelectedSupport (B 0 + t • B 1) (B 1) (selectedAffineSupport B t) := by
  simpa only [affinePairBasis_zero, affinePairBasis_one] using
    selectedSupport_spec (affinePairBasis B t)

theorem selectedAffineSupport_mem_normingFunctionals
    (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) :
    selectedAffineSupport B t ∈ normingFunctionals (B 0 + t • B 1) :=
  (selectedAffineSupport_spec B t).1

/-- Independent choices of actual norming supports converge to the
selected support as their affine parameter approaches any point from
the right. -/
theorem normingSupport_tendsto_selectedAffineSupport_of_tendsto
    (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) {ι : Type*} {l : Filter ι}
    (t : ι → ℝ) (ht : Tendsto t l (𝓝[>] s))
    (f : ι → StrongDual ℝ E)
    (hf : ∀ᶠ i in l, f i ∈ normingFunctionals (B 0 + t i • B 1)) :
    Tendsto f l (𝓝 (selectedAffineSupport B s)) := by
  have hdisplacement : Tendsto (fun i => t i - s) l (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Tendsto (fun _ : ι => s) l (𝓝 s) := tendsto_const_nhds
      simpa only [sub_self] using ((tendsto_nhdsWithin_iff.mp ht).1.sub hc)
    · filter_upwards [(tendsto_nhdsWithin_iff.mp ht).2] with i hi
      change s < t i at hi
      change 0 < t i - s
      exact sub_pos.mpr hi
  apply normingSupport_tendsto_selectedSupport_of_tendsto (affinePairBasis B s)
    (fun i => t i - s) hdisplacement f
  filter_upwards [hf] with i hi
  have hline : affinePairBasis B s 0 + (t i - s) • affinePairBasis B s 1 =
      B 0 + t i • B 1 := by
    rw [affinePairBasis_zero, affinePairBasis_one]
    module
  rwa [hline]

/-- Actual right-continuity of the selected functional in the strong
dual's operator-norm topology. -/
theorem selectedAffineSupport_tendsto_right
    (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) :
    Tendsto (selectedAffineSupport B) (𝓝[>] s) (𝓝 (selectedAffineSupport B s)) := by
  exact normingSupport_tendsto_selectedAffineSupport_of_tendsto B s id tendsto_id
    (selectedAffineSupport B)
    (Eventually.of_forall (selectedAffineSupport_mem_normingFunctionals B))

theorem selectedAffineSupport_continuousWithinAt_right
    (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) :
    ContinuousWithinAt (selectedAffineSupport B) (Ioi s) s :=
  selectedAffineSupport_tendsto_right B s

/-- On a continuous angle branch the actual selected support angle has
the same proved right-continuity. The branch condition is only at the
limit functional. -/
theorem supportAngle_selectedAffineSupport_tendsto_right
    (B C : Module.Basis (Fin 2) ℝ E) (s : ℝ)
    (hpos : 0 < selectedAffineSupport B s (C 0) + selectedAffineSupport B s (C 1)) :
    Tendsto (fun t : ℝ => supportAngle C (selectedAffineSupport B t)) (𝓝[>] s)
      (𝓝 (supportAngle C (selectedAffineSupport B s))) :=
  (supportAngle_continuousAt_of_sum_pos C (selectedAffineSupport B s) hpos).tendsto.comp
    (selectedAffineSupport_tendsto_right B s)

theorem supportAngle_selectedAffineSupport_continuousWithinAt_right
    (B C : Module.Basis (Fin 2) ℝ E) (s : ℝ)
    (hpos : 0 < selectedAffineSupport B s (C 0) + selectedAffineSupport B s (C 1)) :
    ContinuousWithinAt (fun t : ℝ => supportAngle C (selectedAffineSupport B t)) (Ioi s) s :=
  supportAngle_selectedAffineSupport_tendsto_right B C s hpos

end Markov
