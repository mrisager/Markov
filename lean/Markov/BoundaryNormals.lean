import Markov.BoundaryArc
import Markov.NormalArcClosure

/-! Euclidean normals of actual subsets of a normed plane. The local
boundary slope arc is the radial section, so its genuine normals contain
the selected endpoint normal in their closure. No identification with a
global cutoff component is asserted here. -/

noncomputable section
open Set

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual normalized support normals at points of `S`, measured in the
Euclidean covector coordinates of `C`. -/
def normalsOn (C : Module.Basis (Fin 2) ℝ E) (S : Set E) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {n | ∃ x ∈ S, ∃ f ∈ normingFunctionals x, n = normalizedEuclideanCovector C f}

theorem normalsOn_mono (C : Module.Basis (Fin 2) ℝ E) {S T : Set E}
    (hST : S ⊆ T) : normalsOn C S ⊆ normalsOn C T := by
  rintro n ⟨x, hx, f, hf, hn⟩
  exact ⟨x, hST hx, f, hf, hn⟩

/-- At unit-sphere points these actual Euclidean normals have unit length. -/
theorem norm_eq_one_of_mem_normalsOn (C : Module.Basis (Fin 2) ℝ E)
    (S : Set E) (hS : ∀ x ∈ S, ‖x‖ = 1)
    (n : EuclideanSpace ℝ (Fin 2)) (hn : n ∈ normalsOn C S) : ‖n‖ = 1 := by
  obtain ⟨x, hx, f, hf, rfl⟩ := hn
  apply norm_normalizedEuclideanCovector_of_norming C x _ f hf
  intro hzero
  have hunit := hS x hx
  simp [hzero] at hunit

/-- The boundary arc's normals are exactly all supports over the open
interval of its radial parameterization. -/
theorem normalsOn_slopeBoundaryArc (B C : Module.Basis (Fin 2) ℝ E) (a b : ℝ) :
    normalsOn C (slopeBoundaryArc B a b) =
      normalizedEuclideanCovector C ''
        {f | ∃ t ∈ Set.Ioo a b, f ∈ normingFunctionals (radialBasisSection B t)} := by
  rw [← radialBasisSection_image_Ioo]
  ext n
  constructor
  · rintro ⟨x, ⟨t, ht, rfl⟩, f, hf, rfl⟩
    exact ⟨f, ⟨t, ht, hf⟩, rfl⟩
  · rintro ⟨f, ⟨t, ht, hf⟩, rfl⟩
    exact ⟨radialBasisSection B t, ⟨t, ht, rfl⟩, f, hf, rfl⟩

theorem normalsOn_slopeBoundaryArc_eq_interiorRadialNormals
    (B C : Module.Basis (Fin 2) ℝ E) (ε : ℝ) :
    normalsOn C (slopeBoundaryArc B 0 ε) = interiorRadialNormals B C ε :=
  normalsOn_slopeBoundaryArc B C 0 ε

/-- The selected endpoint normal is a limit of actual normals of the
local unit-ball boundary arc, for any choice of Euclidean coordinate basis. -/
theorem selectedSupport_normal_mem_closure_normalsOn_slopeBoundaryArc
    (B C : Module.Basis (Fin 2) ℝ E) (ε : ℝ) (hε : 0 < ε) :
    normalizedEuclideanCovector C (selectedSupport B) ∈
      closure (normalsOn C (slopeBoundaryArc B 0 ε)) := by
  rw [normalsOn_slopeBoundaryArc_eq_interiorRadialNormals]
  exact selectedSupport_normal_mem_closure_interiorRadialNormals B C ε hε

/-- The same assertion expressed directly on the actual closed-unit-ball
frontier intersected with the open slope wedge. -/
theorem selectedSupport_normal_mem_closure_normalsOn_frontier_wedge
    (B C : Module.Basis (Fin 2) ℝ E) (ε : ℝ) (hε : 0 < ε) :
    normalizedEuclideanCovector C (selectedSupport B) ∈
      closure (normalsOn C (frontier (Metric.closedBall (0 : E) 1) ∩
        {x | 0 < B.coord 0 x ∧ 0 < basisSlope B x ∧ basisSlope B x < ε})) := by
  rw [← slopeBoundaryArc_eq_frontier_wedge]
  exact selectedSupport_normal_mem_closure_normalsOn_slopeBoundaryArc B C ε hε

/-- Independent integral rays give the corresponding actual boundary arc;
the determinant hypothesis certifies their independence. -/
theorem selectedSupportAt_normal_mem_closure_normalsOn_slopeBoundaryArc
    (B C : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ) (hdet : intDet u v ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    normalizedEuclideanCovector C (selectedSupportAt B u v) ∈
      closure (normalsOn C (slopeBoundaryArc (intPairBasis B u v hdet) 0 ε)) := by
  rw [selectedSupportAt, dif_pos hdet]
  exact selectedSupport_normal_mem_closure_normalsOn_slopeBoundaryArc
    (intPairBasis B u v hdet) C ε hε

end Markov
