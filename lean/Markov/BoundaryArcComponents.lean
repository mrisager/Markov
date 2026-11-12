import Markov.BoundaryArcHomeomorph
import Markov.CutoffArcs
import Mathlib.Topology.Connected.Basic

/-! A local slope arc is a maximal connected piece of the actual unit
boundary after removing its endpoints and any further disjoint cutoff set.
The first-coordinate exclusion is an explicit geometric input; no global
cutoff-component identification is assumed. -/

noncomputable section
namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The two unit-boundary points on the zero first-coordinate line are
exactly the two normalized second-basis rays. -/
theorem unit_eq_normalize_basis_one_or_neg
    (B : Module.Basis (Fin 2) ℝ E) (x : E)
    (hunit : ‖x‖ = 1) (hzero : B.coord 0 x = 0) :
    x = NormedSpace.normalize (B 1) ∨ x = -NormedSpace.normalize (B 1) := by
  have hrep : x = (B.coord 1 x) • B 1 := by
    have he : x = (B.coord 0 x) • B 0 + (B.coord 1 x) • B 1 := by
      simpa only [Module.Basis.coord_apply, Fin.sum_univ_two] using (B.sum_repr x).symm
    simpa only [hzero, zero_smul, zero_add] using he
  have hne : B.coord 1 x ≠ 0 := by
    intro hz
    have hxzero : x = 0 := by simpa only [hz, zero_smul] using hrep
    simp [hxzero] at hunit
  have hnorm : x = NormedSpace.normalize ((B.coord 1 x) • B 1) := by
    rw [← hrep, NormedSpace.normalize_eq_self_of_norm_eq_one hunit]
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · right
    exact hnorm.trans (NormedSpace.normalize_smul_of_neg hneg (B 1))
  · left
    exact hnorm.trans (NormedSpace.normalize_smul_of_pos hpos (B 1))

/-- Removing the two normalized second-basis rays excludes zero first
coordinates everywhere on the remaining actual unit boundary. -/
theorem coord_zero_ne_of_mem_boundary_difference
    (B : Module.Basis (Fin 2) ℝ E) (T : Set E)
    (hpos : NormedSpace.normalize (B 1) ∈ T)
    (hneg : -NormedSpace.normalize (B 1) ∈ T)
    (x : E) (hx : x ∈ frontier (Metric.closedBall (0 : E) 1) \ T) :
    B.coord 0 x ≠ 0 := by
  intro hzero
  have hunit : ‖x‖ = 1 := by
    have hfront := hx.1
    rw [frontier_closedBall (0 : E) (by norm_num : (1 : ℝ) ≠ 0)] at hfront
    simpa using hfront
  rcases unit_eq_normalize_basis_one_or_neg B x hunit hzero with he | he
  · exact hx.2 (he.symm ▸ hpos)
  · exact hx.2 (he.symm ▸ hneg)

/-- A preconnected unit-boundary set that avoids the zero first-coordinate
line and the two endpoint rays cannot leave an open slope arc it meets. -/
theorem preconnected_subset_slopeBoundaryArc
    (B : Module.Basis (Fin 2) ℝ E) (a b : ℝ) (S : Set E)
    (hS : IsPreconnected S) (hunit : ∀ x ∈ S, ‖x‖ = 1)
    (hcoord : ∀ x ∈ S, B.coord 0 x ≠ 0)
    (ha : radialBasisSection B a ∉ S) (hb : radialBasisSection B b ∉ S)
    (hmeet : (S ∩ slopeBoundaryArc B a b).Nonempty) :
    S ⊆ slopeBoundaryArc B a b := by
  obtain ⟨x₀, hx₀, hx₀arc⟩ := hmeet
  have hpos : ∀ x ∈ S, 0 < B.coord 0 x := by
    intro x hx
    exact hS.lt_of_ne (continuous_basisCoord B 0).continuousOn hcoord
      ⟨x₀, hx₀, hx₀arc.2.1⟩ hx
  have hcont : ContinuousOn (basisSlope B) S := by
    intro x hx
    exact (basisSlope_continuousAt B x (hpos x hx).ne').continuousWithinAt
  have hneq (r : ℝ) (hr : radialBasisSection B r ∉ S) :
      ∀ x ∈ S, basisSlope B x ≠ r := by
    intro x hx hxr
    have hinv := radialBasisSection_basisSlope B x (hunit x hx) (hpos x hx)
    rw [hxr] at hinv
    exact hr (hinv.symm ▸ hx)
  intro x hx
  exact ⟨hunit x hx, hpos x hx,
    hS.lt_of_ne hcont (hneq a ha) ⟨x₀, hx₀, hx₀arc.2.2.1⟩ hx,
    hS.gt_of_ne hcont (hneq b hb) ⟨x₀, hx₀, hx₀arc.2.2.2⟩ hx⟩

/-- With the coordinate exclusion kept explicit, a cutoff-disjoint local
arc is exactly the connected component of every one of its points in the
actual unit-ball boundary with the cutoff set removed. -/
theorem connectedComponentIn_boundary_difference_eq_slopeBoundaryArc
    (B : Module.Basis (Fin 2) ℝ E) (a b t : ℝ) (T : Set E)
    (ht : t ∈ Set.Ioo a b)
    (ha : radialBasisSection B a ∈ T) (hb : radialBasisSection B b ∈ T)
    (hdisj : Disjoint (slopeBoundaryArc B a b) T)
    (hcoord : ∀ x ∈ frontier (Metric.closedBall (0 : E) 1) \ T,
      B.coord 0 x ≠ 0) :
    connectedComponentIn (frontier (Metric.closedBall (0 : E) 1) \ T)
      (radialBasisSection B t) = slopeBoundaryArc B a b := by
  let M : Set E := frontier (Metric.closedBall (0 : E) 1) \ T
  have hArcM : slopeBoundaryArc B a b ⊆ M := by
    intro x hx
    refine ⟨?_, Set.disjoint_left.mp hdisj hx⟩
    rw [frontier_closedBall (0 : E) (by norm_num : (1 : ℝ) ≠ 0)]
    simpa using hx.1
  have htArc : radialBasisSection B t ∈ slopeBoundaryArc B a b := by
    rw [← radialBasisSection_image_Ioo]
    exact Set.mem_image_of_mem _ ht
  have htM : radialBasisSection B t ∈ M := hArcM htArc
  apply Set.Subset.antisymm
  · apply preconnected_subset_slopeBoundaryArc B a b
      (connectedComponentIn M (radialBasisSection B t))
      isPreconnected_connectedComponentIn
    · intro x hx
      have hfront := (connectedComponentIn_subset M (radialBasisSection B t) hx).1
      rw [frontier_closedBall (0 : E) (by norm_num : (1 : ℝ) ≠ 0)] at hfront
      simpa using hfront
    · intro x hx
      exact hcoord x (connectedComponentIn_subset M (radialBasisSection B t) hx)
    · intro hx
      exact (connectedComponentIn_subset M (radialBasisSection B t) hx).2 ha
    · intro hx
      exact (connectedComponentIn_subset M (radialBasisSection B t) hx).2 hb
    · exact ⟨radialBasisSection B t, mem_connectedComponentIn htM, htArc⟩
  · exact (slopeBoundaryArc_isPreconnected B a b).subset_connectedComponentIn htArc hArcM

/-- Endpoint cuts and the two second-basis axis cuts suffice to identify
the actual cutoff-disjoint slope arc with its maximal connected component. -/
theorem connectedComponentIn_boundary_difference_eq_slopeBoundaryArc_of_axis_cuts
    (B : Module.Basis (Fin 2) ℝ E) (a b t : ℝ) (T : Set E)
    (ht : t ∈ Set.Ioo a b)
    (ha : radialBasisSection B a ∈ T) (hb : radialBasisSection B b ∈ T)
    (hpos : NormedSpace.normalize (B 1) ∈ T)
    (hneg : -NormedSpace.normalize (B 1) ∈ T)
    (hdisj : Disjoint (slopeBoundaryArc B a b) T) :
    connectedComponentIn (frontier (Metric.closedBall (0 : E) 1) \ T)
      (radialBasisSection B t) = slopeBoundaryArc B a b :=
  connectedComponentIn_boundary_difference_eq_slopeBoundaryArc B a b t T ht ha hb hdisj
    (coord_zero_ne_of_mem_boundary_difference B T hpos hneg)

/-- At every nonempty height cutoff the two second-basis axis points
belong to the actual primitive cutoff set. -/
theorem basis_one_axis_mem_cutoffCorners
    (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) (hH : 1 ≤ H) :
    NormedSpace.normalize (B 1) ∈ cutoffCorners B H ∧
      -NormedSpace.normalize (B 1) ∈ cutoffCorners B H := by
  classical
  have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hp : ((0, 1) : ℤ × ℤ) ∈ primitiveDirectionsUpTo H := by
    apply (mem_primitiveDirectionsUpTo H (0, 1)).mpr
    exact ⟨by norm_num, by simpa [intHeight] using hHreal⟩
  have hn : ((0, -1) : ℤ × ℤ) ∈ primitiveDirectionsUpTo H := by
    apply (mem_primitiveDirectionsUpTo H (0, -1)).mpr
    exact ⟨by norm_num, by simpa [intHeight] using hHreal⟩
  constructor
  · have hm : NormedSpace.normalize (intVector B (0, 1)) ∈ cutoffCorners B H :=
      Finset.mem_image.mpr ⟨(0, 1), hp, rfl⟩
    simpa [intVector] using hm
  · have hm : NormedSpace.normalize (intVector B (0, -1)) ∈ cutoffCorners B H :=
      Finset.mem_image.mpr ⟨(0, -1), hn, rfl⟩
    simpa [intVector, NormedSpace.normalize_neg] using hm

/-- The canonical-sector gap between actual consecutive primitive cutoff
directions is exactly the maximal connected component of the unit-ball
boundary with all actual primitive cutoff points removed. -/
theorem consecutiveCutoffSlopes_connectedComponentIn_eq_arc
    (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H u v) (t : ℝ)
    (ht : t ∈ Set.Ioo (cutoffSlope u) (cutoffSlope v)) :
    connectedComponentIn
      (frontier (Metric.closedBall (0 : E) 1) \ (↑(cutoffCorners B H) : Set E))
      (radialBasisSection B t) =
        slopeBoundaryArc B (cutoffSlope u) (cutoffSlope v) := by
  have hup := ((mem_cutoffSlopesUpTo H u).mp h.1).1
  have hvp := ((mem_cutoffSlopesUpTo H v).mp h.2.1).1
  have hH : 1 ≤ H := by
    have huH := ((mem_cutoffSlopesUpTo H u).mp h.1).2.2.2.1
    omega
  have haxes := basis_one_axis_mem_cutoffCorners B H hH
  have hu : radialBasisSection B (cutoffSlope u) ∈ cutoffCorners B H := by
    rw [← normalize_intVector_eq_radialBasisSection B u hup]
    exact normalize_mem_cutoffCorners B H u h.1
  have hv : radialBasisSection B (cutoffSlope v) ∈ cutoffCorners B H := by
    rw [← normalize_intVector_eq_radialBasisSection B v hvp]
    exact normalize_mem_cutoffCorners B H v h.2.1
  exact connectedComponentIn_boundary_difference_eq_slopeBoundaryArc_of_axis_cuts
    B (cutoffSlope u) (cutoffSlope v) t (↑(cutoffCorners B H) : Set E) ht hu hv
    haxes.1 haxes.2 (consecutiveCutoffSlopes_arc_disjoint_corners B H u v h)

end Markov
