import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Tactic

/-! Exact metric equality cases for the actual upper half-plane: the log-height
lower bound and a triangle with two endpoints on one vertical line.
No local-to-global geodesic or simplicity assertion is made. -/

noncomputable section
open Set
namespace Markov

/-- Equality in the actual log-height distance lower bound holds exactly
when the two points have the same real coordinate. -/
theorem upperHalfPlane_dist_log_im_eq_iff (z w : UpperHalfPlane) :
    dist (Real.log z.im) (Real.log w.im) = dist z w ↔ z.re = w.re := by
  let v : UpperHalfPlane := UpperHalfPlane.mk ⟨z.re, w.im⟩ w.im_pos
  have hvre : v.re = z.re := rfl
  have hvim : v.im = w.im := rfl
  have hvdist : dist z v = dist (Real.log z.im) (Real.log w.im) := by
    exact UpperHalfPlane.dist_of_re_eq rfl
  constructor
  · intro he
    have hc := congrArg Real.cosh (he.symm.trans hvdist.symm)
    rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist', hvre, hvim] at hc
    have hden : 2 * z.im * w.im ≠ 0 := by positivity
    have hn := (div_left_inj' hden).mp hc
    have hs : (z.re - w.re) ^ 2 = 0 := by nlinarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  · intro hre
    exact (UpperHalfPlane.dist_of_re_eq hre).symm

private theorem real_dist_triangle_eq_iff_mem_uIcc (a b c : ℝ) :
    dist a b + dist b c = dist a c ↔ b ∈ Set.uIcc a c := by
  rw [dist_add_dist_eq_iff]
  rcases le_total a c with hac | hca
  · rw [wbtw_iff_of_le hac, Set.uIcc_of_le hac]
    rfl
  · rw [wbtw_comm, wbtw_iff_of_le hca, Set.uIcc_comm a c, Set.uIcc_of_le hca]
    rfl

/-- For two actual vertical endpoints, hyperbolic triangle equality holds
exactly on their vertical segment, with log-height between the endpoint logs.
The endpoint order and coincident-endpoint case are both retained. -/
theorem upperHalfPlane_vertical_triangle_eq_iff
    (z x w : UpperHalfPlane) (hre : z.re = w.re) :
    dist z x + dist x w = dist z w ↔
      x.re = z.re ∧ Real.log x.im ∈ Set.uIcc (Real.log z.im) (Real.log w.im) := by
  constructor
  · intro he
    have hzlower := UpperHalfPlane.dist_log_im_le z x
    have hxlower := UpperHalfPlane.dist_log_im_le x w
    have htriangle := dist_triangle (Real.log z.im) (Real.log x.im) (Real.log w.im)
    have hzw := UpperHalfPlane.dist_of_re_eq hre
    have hzeq : dist (Real.log z.im) (Real.log x.im) = dist z x := by linarith
    have hzre := (upperHalfPlane_dist_log_im_eq_iff z x).mp hzeq
    refine ⟨hzre.symm, (real_dist_triangle_eq_iff_mem_uIcc _ _ _).mp ?_⟩
    linarith
  · rintro ⟨hxre, hbetween⟩
    rw [UpperHalfPlane.dist_of_re_eq hxre.symm,
      UpperHalfPlane.dist_of_re_eq (hxre.trans hre), UpperHalfPlane.dist_of_re_eq hre]
    exact (real_dist_triangle_eq_iff_mem_uIcc _ _ _).mpr hbetween

end Markov
