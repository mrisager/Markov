import Markov.AffineSupport

/-! The actual support selected from the decreasing side of an affine
section. Reversing the second basis vector constructs the minimizer of
the second evaluation. Its one-sided limit follows from the already
checked support-limit theorem; no left-continuity assumption is made. -/

noncomputable section
open Set Filter
open scoped Topology

namespace Markov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def reverseSecondBasis (B : Module.Basis (Fin 2) ℝ E) : Module.Basis (Fin 2) ℝ E :=
  intPairBasis B (1, 0) (0, -1) (by norm_num [intDet])

@[simp] theorem reverseSecondBasis_zero (B : Module.Basis (Fin 2) ℝ E) :
    reverseSecondBasis B 0 = B 0 := by
  simp [reverseSecondBasis, intPairBasis_zero, intVector]

@[simp] theorem reverseSecondBasis_one (B : Module.Basis (Fin 2) ℝ E) :
    reverseSecondBasis B 1 = -B 1 := by
  simp [reverseSecondBasis, intPairBasis_one, intVector]

def leftSelectedAffineSupport (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) : StrongDual ℝ E :=
  selectedSupport (reverseSecondBasis (affinePairBasis B t))

theorem leftSelectedAffineSupport_spec (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) :
    IsSelectedSupport (B 0 + t • B 1) (-B 1) (leftSelectedAffineSupport B t) := by
  simpa only [reverseSecondBasis_zero, reverseSecondBasis_one,
    affinePairBasis_zero, affinePairBasis_one] using
    selectedSupport_spec (reverseSecondBasis (affinePairBasis B t))

theorem leftSelectedAffineSupport_mem_normingFunctionals
    (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) :
    leftSelectedAffineSupport B t ∈ normingFunctionals (B 0 + t • B 1) :=
  (leftSelectedAffineSupport_spec B t).1

theorem leftSelectedAffineSupport_eval_le (B : Module.Basis (Fin 2) ℝ E)
    (t : ℝ) (f : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals (B 0 + t • B 1)) :
    leftSelectedAffineSupport B t (B 1) ≤ f (B 1) := by
  simpa only [map_neg, neg_le_neg_iff] using (leftSelectedAffineSupport_spec B t).2 f hf

/-- Every selection of norming supports has the same limit from the left. -/
theorem normingSupport_tendsto_leftSelectedAffineSupport_of_tendsto
    (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) {ι : Type*} {l : Filter ι}
    (t : ι → ℝ) (ht : Tendsto t l (𝓝[<] s))
    (f : ι → StrongDual ℝ E)
    (hf : ∀ᶠ i in l, f i ∈ normingFunctionals (B 0 + t i • B 1)) :
    Tendsto f l (𝓝 (leftSelectedAffineSupport B s)) := by
  have hdisplacement : Tendsto (fun i => s - t i) l (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Tendsto (fun _ : ι => s) l (𝓝 s) := tendsto_const_nhds
      simpa only [sub_self] using (hc.sub (tendsto_nhdsWithin_iff.mp ht).1)
    · filter_upwards [(tendsto_nhdsWithin_iff.mp ht).2] with i hi
      change t i < s at hi
      change 0 < s - t i
      exact sub_pos.mpr hi
  apply normingSupport_tendsto_selectedSupport_of_tendsto
    (reverseSecondBasis (affinePairBasis B s)) (fun i => s - t i) hdisplacement f
  filter_upwards [hf] with i hi
  have hline : reverseSecondBasis (affinePairBasis B s) 0 +
      (s - t i) • reverseSecondBasis (affinePairBasis B s) 1 = B 0 + t i • B 1 := by
    rw [reverseSecondBasis_zero, reverseSecondBasis_one,
      affinePairBasis_zero, affinePairBasis_one]
    module
  rwa [hline]

theorem selectedAffineSupport_tendsto_left (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) :
    Tendsto (selectedAffineSupport B) (𝓝[<] s) (𝓝 (leftSelectedAffineSupport B s)) :=
  normingSupport_tendsto_leftSelectedAffineSupport_of_tendsto B s id tendsto_id
    (selectedAffineSupport B)
    (Eventually.of_forall (selectedAffineSupport_mem_normingFunctionals B))

theorem supportAngle_selectedAffineSupport_tendsto_left
    (B C : Module.Basis (Fin 2) ℝ E) (s : ℝ)
    (hpos : 0 < leftSelectedAffineSupport B s (C 0) +
      leftSelectedAffineSupport B s (C 1)) :
    Tendsto (fun t : ℝ => supportAngle C (selectedAffineSupport B t)) (𝓝[<] s)
      (𝓝 (supportAngle C (leftSelectedAffineSupport B s))) :=
  (supportAngle_continuousAt_of_sum_pos C (leftSelectedAffineSupport B s) hpos).tendsto.comp
    (selectedAffineSupport_tendsto_left B s)

end Markov
