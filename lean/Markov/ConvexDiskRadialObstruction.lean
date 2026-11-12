import Markov.NormalizedCircleDiskObstruction
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Module.Normalize

/-! Actual radial gauge homeomorphisms for bounded convex neighborhoods of zero.
Their literal positive radial factors give the normalized frontier formula and
pull back the checked disk-extension obstruction. No crossing/separation theorem
or boundary winding field is assumed. -/

noncomputable section
open Set Topology Metric
namespace Markov

/-- The actual ambient radial gauge homeomorphism from the unit ball to P. -/
def convexDiskRadialHomeomorph (P : Set ℂ) (hc : Convex ℝ P)
    (h0 : P ∈ 𝓝 0) (hb : Bornology.IsBounded P) : ℂ ≃ₜ ℂ :=
  gaugeRescaleHomeomorph (ball (0 : ℂ) 1) P (convex_ball 0 1)
    (ball_mem_nhds 0 (by norm_num))
    (NormedSpace.isVonNBounded_of_isBounded ℝ isBounded_ball)
    hc h0 (NormedSpace.isVonNBounded_of_isBounded ℝ hb)

/-- Its actual image of the closed unit disk is exactly closure P. -/
theorem convexDiskRadialHomeomorph_image_closedBall (P : Set ℂ) (hc : Convex ℝ P)
    (h0 : P ∈ 𝓝 0) (hb : Bornology.IsBounded P) :
    convexDiskRadialHomeomorph P hc h0 hb '' closedBall (0 : ℂ) 1 = closure P := by
  simpa only [convexDiskRadialHomeomorph, closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using
    image_gaugeRescaleHomeomorph_closure (convex_ball (0 : ℂ) 1)
      (ball_mem_nhds 0 (by norm_num))
      (NormedSpace.isVonNBounded_of_isBounded ℝ isBounded_ball)
      hc h0 (NormedSpace.isVonNBounded_of_isBounded ℝ hb)

/-- The actual unit circle maps onto precisely the frontier of P. -/
theorem convexDiskRadialHomeomorph_image_frontier (P : Set ℂ) (hc : Convex ℝ P)
    (h0 : P ∈ 𝓝 0) (hb : Bornology.IsBounded P) :
    convexDiskRadialHomeomorph P hc h0 hb '' sphere (0 : ℂ) 1 = frontier P := by
  rw [← frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0), frontier, image_diff
    (convexDiskRadialHomeomorph P hc h0 hb).injective]
  rw [show interior (ball (0 : ℂ) 1) = ball (0 : ℂ) 1 from isOpen_ball.interior_eq]
  have hi := image_gaugeRescaleHomeomorph_interior (convex_ball (0 : ℂ) 1)
    (ball_mem_nhds 0 (by norm_num))
    (NormedSpace.isVonNBounded_of_isBounded ℝ isBounded_ball)
    hc h0 (NormedSpace.isVonNBounded_of_isBounded ℝ hb)
  have hk := image_gaugeRescaleHomeomorph_closure (convex_ball (0 : ℂ) 1)
    (ball_mem_nhds 0 (by norm_num))
    (NormedSpace.isVonNBounded_of_isBounded ℝ isBounded_ball)
    hc h0 (NormedSpace.isVonNBounded_of_isBounded ℝ hb)
  change convexDiskRadialHomeomorph P hc h0 hb '' closure (ball (0 : ℂ) 1) \
    convexDiskRadialHomeomorph P hc h0 hb '' ball (0 : ℂ) 1 = closure P \ interior P
  change convexDiskRadialHomeomorph P hc h0 hb '' interior (ball (0 : ℂ) 1) = interior P at hi
  rw [isOpen_ball.interior_eq] at hi
  exact congrArg₂ (fun A B : Set ℂ => A \ B) hk hi

/-- The displayed inverse-gauge radial scalar is strictly positive on the
actual unit circle; positivity follows from neighborhood and boundedness. -/
theorem convexDiskRadialHomeomorph_circle_factor_pos (P : Set ℂ)
    (h0 : P ∈ 𝓝 0) (hb : Bornology.IsBounded P) (z : Circle) :
    0 < (gauge P (z : ℂ))⁻¹ := by
  apply inv_pos.mpr
  exact (gauge_pos (absorbent_nhds_zero h0)
    (NormedSpace.isVonNBounded_of_isBounded ℝ hb)).mpr z.coe_ne_zero

/-- The actual boundary image has exactly this positive radial scalar. -/
theorem convexDiskRadialHomeomorph_circle_apply (P : Set ℂ) (hc : Convex ℝ P)
    (h0 : P ∈ 𝓝 0) (hb : Bornology.IsBounded P) (z : Circle) :
    convexDiskRadialHomeomorph P hc h0 hb (z : ℂ) =
      (gauge P (z : ℂ))⁻¹ • (z : ℂ) := by
  change gaugeRescale (ball (0 : ℂ) 1) P (z : ℂ) = _
  simp only [gaugeRescale, gauge_unit_ball, Circle.norm_coe, one_div]

/-- Normalizing the actual radial boundary image is literally the original
unit circle point. No degree or winding identity is postulated. -/
theorem convexDiskRadialHomeomorph_normalize_circle (P : Set ℂ) (hc : Convex ℝ P)
    (h0 : P ∈ 𝓝 0) (hb : Bornology.IsBounded P) (z : Circle) :
    NormedSpace.normalize (convexDiskRadialHomeomorph P hc h0 hb (z : ℂ)) = (z : ℂ) := by
  rw [convexDiskRadialHomeomorph_circle_apply,
    NormedSpace.normalize_smul_of_pos (convexDiskRadialHomeomorph_circle_factor_pos P h0 hb z)]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one z.norm_coe

/-- The actual radial homeomorphism restricted to the closed disk. No closedness
of P is required: the target is its actual closure. -/
def convexDiskRadialClosedDiskHomeomorph (P : Set ℂ) (hc : Convex ℝ P)
    (h0 : P ∈ 𝓝 0) (hb : Bornology.IsBounded P) : ComplexClosedUnitDisk ≃ₜ ↥(closure P) :=
  ((convexDiskRadialHomeomorph P hc h0 hb).image (closedBall (0 : ℂ) 1)).trans
    (Homeomorph.setCongr (convexDiskRadialHomeomorph_image_closedBall P hc h0 hb))

/-- The actual radial homeomorphism restricted to the literal complex circle. -/
def convexDiskRadialBoundaryHomeomorph (P : Set ℂ) (hc : Convex ℝ P)
    (h0 : P ∈ 𝓝 0) (hb : Bornology.IsBounded P) : Circle ≃ₜ ↥(frontier P) :=
  ((convexDiskRadialHomeomorph P hc h0 hb).image (sphere (0 : ℂ) 1)).trans
    (Homeomorph.setCongr (convexDiskRadialHomeomorph_image_frontier P hc h0 hb))

/-- There is no actual continuous extension over closure P of its normalized
radial boundary direction, transported by the actual inverse circle homeomorphism.
All hypotheses on P are concrete convexity, neighborhood, and boundedness. -/
theorem convexDisk_no_continuous_normalized_boundary_extension (P : Set ℂ)
    (hc : Convex ℝ P) (h0 : P ∈ 𝓝 0) (hb : Bornology.IsBounded P)
    (r : ↥(closure P) → NormalizedCircle) (hr : Continuous r)
    (hboundary : ∀ z : ↥(frontier P),
      ((AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0))
        (r ⟨z.val, frontier_subset_closure z.property⟩) : ℂ) = NormedSpace.normalize z.val) :
    False := by
  let e := convexDiskRadialClosedDiskHomeomorph P hc h0 hb
  apply normalizedCircle_no_continuous_disk_boundary_extension
    (fun z => r (e z)) (hr.comp e.continuous)
  intro z
  apply (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).injective
  apply Circle.coe_injective
  rw [Homeomorph.apply_symm_apply]
  have hz := hboundary (convexDiskRadialBoundaryHomeomorph P hc h0 hb z)
  have he : e (complexUnitCircleClosedDisk z) =
      ⟨(convexDiskRadialBoundaryHomeomorph P hc h0 hb z).val,
        frontier_subset_closure (convexDiskRadialBoundaryHomeomorph P hc h0 hb z).property⟩ := rfl
  rw [he]
  rw [hz]
  exact convexDiskRadialHomeomorph_normalize_circle P hc h0 hb z

end Markov
