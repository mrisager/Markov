import Markov.RealSectorCoverage
import Markov.SignedCutoffComponents

/-! Every point of the actual unit boundary outside the primitive cutoff
lies in one of the signed consecutive cutoff components. The source norm
and cutoff set remain unchanged throughout the coordinate changes. -/

noncomputable section
namespace Markov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem uncut_boundary_exists_signed_cutoff_component
    (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) (hH : 1 ≤ H) (x : E)
    (hx : x ∈ frontier (Metric.closedBall (0 : E) 1) \ (↑(cutoffCorners B H) : Set E)) :
    ∃ (k : Fin 8) (u v : ℤ × ℤ), ConsecutiveCutoffSlopes H u v ∧
      x ∈ slopeBoundaryArc (signedSectorBasis B k) (cutoffSlope u) (cutoffSlope v) ∧
      connectedComponentIn
        (frontier (Metric.closedBall (0 : E) 1) \ (↑(cutoffCorners B H) : Set E)) x =
        slopeBoundaryArc (signedSectorBasis B k) (cutoffSlope u) (cutoffSlope v) := by
  have hnorm : ‖x‖ = 1 := by
    have hf := hx.1
    rw [frontier_closedBall (0 : E) (by norm_num : (1 : ℝ) ≠ 0)] at hf
    simpa using hf
  obtain ⟨k, t, ht, hrad⟩ := exists_signedSectorBasis_radial_of_uncut B H hH x hnorm hx.2
  have havoid : ∀ w ∈ cutoffSlopesUpTo H, cutoffSlope w ≠ t := by
    intro w hw hwt
    have hm := normalize_mem_cutoffCorners (signedSectorBasis B k) H w hw
    rw [normalize_intVector_eq_radialBasisSection (signedSectorBasis B k) w
      ((mem_cutoffSlopesUpTo H w).mp hw).1, hwt, hrad,
      cutoffCorners_signedSectorBasis] at hm
    exact hx.2 hm
  obtain ⟨u, v, huv, hbetween⟩ := exists_consecutiveCutoffSlopes_bracketing H hH t ht havoid
  have hcomp := consecutiveCutoffSlopes_connectedComponentIn_eq_arc
    (signedSectorBasis B k) H u v huv t hbetween
  rw [cutoffCorners_signedSectorBasis, hrad] at hcomp
  refine ⟨k, u, v, huv, ?_, hcomp⟩
  rw [← radialBasisSection_image_Ioo]
  exact ⟨t, hbetween, hrad⟩

end Markov
