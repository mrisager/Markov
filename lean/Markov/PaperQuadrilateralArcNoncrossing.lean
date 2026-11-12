import Markov.PaperQuadrilateralDiskChart
import Markov.DiskArcTransverseCrossing

/-! Endpoint chord noncrossing is derived from actual disjoint proper Q-arcs.
The disk coordinate, actual frontier endpoints, actual strict interiors, and
actual disjoint images are used directly. There is no assumed matching or
boundary-order field and no normal-form/classification conclusion. -/

noncomputable section
open Set Topology
namespace Markov

private theorem qArc_interval_interior (t : unitInterval) (ht : ¬(t=0 ∨ t=1)) :
    0 < (t:ℝ) ∧ (t:ℝ) < 1 := by
  have h0 : (t:ℝ) ≠ 0 := fun h => ht (Or.inl (Subtype.ext h))
  have h1 : (t:ℝ) ≠ 1 := fun h => ht (Or.inr (Subtype.ext h))
  exact ⟨lt_of_le_of_ne t.property.1 h0.symm, lt_of_le_of_ne t.property.2 h1⟩

private theorem qArc_endpoint_frontier (f : unitInterval → paperIdealQuadrilateral)
    (hf0 : (f 0:UpperHalfPlane) ∈ frontier paperIdealQuadrilateral)
    (hf1 : (f 1:UpperHalfPlane) ∈ frontier paperIdealQuadrilateral)
    (s : unitInterval) (hs : s=0 ∨ s=1) :
    (f s:UpperHalfPlane) ∈ frontier paperIdealQuadrilateral := by
  rcases hs with rfl | rfl
  · exact hf0
  · exact hf1

/-- Two actual proper Q-arcs with disjoint open images cannot have a transverse
interior intersection of their endpoint chords in the constructed actual disk
coordinate. Endpoint-only arc intersections are explicitly excluded in the proof. -/
theorem paperQuadrilateral_disjoint_proper_arcs_no_transverse_chord_crossing
    (f g : unitInterval → paperIdealQuadrilateral) (hf : Continuous f) (hg : Continuous g)
    (hf0 : (f 0:UpperHalfPlane) ∈ frontier paperIdealQuadrilateral)
    (hf1 : (f 1:UpperHalfPlane) ∈ frontier paperIdealQuadrilateral)
    (hg0 : (g 0:UpperHalfPlane) ∈ frontier paperIdealQuadrilateral)
    (hg1 : (g 1:UpperHalfPlane) ∈ frontier paperIdealQuadrilateral)
    (hfn : f 0 ≠ f 1) (hgn : g 0 ≠ g 1)
    (hfi : ∀ s : unitInterval, 0 < (s:ℝ) → (s:ℝ) < 1 →
      (f s:UpperHalfPlane) ∈ paperIdealQuadrilateralStrictRegion)
    (hgi : ∀ s : unitInterval, 0 < (s:ℝ) → (s:ℝ) < 1 →
      (g s:UpperHalfPlane) ∈ paperIdealQuadrilateralStrictRegion)
    (hend : ∀ s t : unitInterval, (s=0 ∨ s=1) → (t=0 ∨ t=1) → f s ≠ g t)
    (hdisj : Disjoint (f '' Ioo (0:unitInterval) 1) (g '' Ioo (0:unitInterval) 1))
    (hd : ((paperQuadrilateralDiskCoordinate (f 1)-paperQuadrilateralDiskCoordinate (f 0)).re *
        (paperQuadrilateralDiskCoordinate (g 1)-paperQuadrilateralDiskCoordinate (g 0)).im -
      (paperQuadrilateralDiskCoordinate (f 1)-paperQuadrilateralDiskCoordinate (f 0)).im *
        (paperQuadrilateralDiskCoordinate (g 1)-paperQuadrilateralDiskCoordinate (g 0)).re) ≠ 0)
    (u v : unitInterval) (hu0 : 0 < (u:ℝ)) (hu1 : (u:ℝ) < 1)
    (hv0 : 0 < (v:ℝ)) (hv1 : (v:ℝ) < 1)
    (hchord : diskArcChord (paperQuadrilateralDiskCoordinate ∘ f) u =
      diskArcChord (paperQuadrilateralDiskCoordinate ∘ g) v) : False := by
  obtain ⟨s, t, heq⟩ := diskArcs_intersect_of_transverse_interior_chords
    (paperQuadrilateralDiskCoordinate ∘ f) (paperQuadrilateralDiskCoordinate ∘ g)
    (continuous_paperQuadrilateralDiskCoordinate.comp hf) (continuous_paperQuadrilateralDiskCoordinate.comp hg)
    (paperQuadrilateralDiskCoordinate_norm_eq_one_of_frontier _ hf0)
    (paperQuadrilateralDiskCoordinate_norm_eq_one_of_frontier _ hf1)
    (fun h => hfn (paperQuadrilateralDiskCoordinate_injective h))
    (paperQuadrilateralDiskCoordinate_norm_eq_one_of_frontier _ hg0)
    (paperQuadrilateralDiskCoordinate_norm_eq_one_of_frontier _ hg1)
    (fun h => hgn (paperQuadrilateralDiskCoordinate_injective h))
    (fun s hs0 hs1 => paperQuadrilateralDiskCoordinate_norm_lt_one_of_strict _ (hfi s hs0 hs1))
    (fun s hs0 hs1 => paperQuadrilateralDiskCoordinate_norm_lt_one_of_strict _ (hgi s hs0 hs1))
    (fun s t hs ht h => hend s t hs ht (paperQuadrilateralDiskCoordinate_injective h))
    hd u v hu0 hu1 hv0 hv1 hchord
  have hq : f s = g t := paperQuadrilateralDiskCoordinate_injective heq
  by_cases hs : s=0 ∨ s=1
  · by_cases ht : t=0 ∨ t=1
    · exact hend s t hs ht hq
    · obtain ⟨ht0, ht1⟩ := qArc_interval_interior t ht
      have hfront : (g t:UpperHalfPlane) ∈ frontier paperIdealQuadrilateral :=
        hq ▸ qArc_endpoint_frontier f hf0 hf1 s hs
      exact hfront.2 (paperIdealQuadrilateralStrictRegion_subset_interior (hgi t ht0 ht1))
  · obtain ⟨hs0, hs1⟩ := qArc_interval_interior s hs
    by_cases ht : t=0 ∨ t=1
    · have hfront : (f s:UpperHalfPlane) ∈ frontier paperIdealQuadrilateral :=
        hq.symm ▸ qArc_endpoint_frontier g hg0 hg1 t ht
      exact hfront.2 (paperIdealQuadrilateralStrictRegion_subset_interior (hfi s hs0 hs1))
    · obtain ⟨ht0, ht1⟩ := qArc_interval_interior t ht
      exact disjoint_left.mp hdisj ⟨s, ⟨hs0, hs1⟩, rfl⟩ ⟨t, ⟨ht0, ht1⟩, hq.symm⟩

end Markov
