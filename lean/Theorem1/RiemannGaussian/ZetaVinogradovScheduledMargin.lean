/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovHeightSchedule
import RiemannGaussian.ZetaVinogradovMargin
import RiemannGaussian.ZetaLogLogBudget

/-!
# The full Vinogradov margin on one height-dependent schedule

The natural degree, both oscillatory profiles, center allowance and
original height threshold are paid on the same schedule. The resulting
width has the classical Vinogradov--Korobov logarithmic powers and an
explicit conservative coefficient. Its starting height is existential.
-/

namespace RiemannGaussian.ZetaVinogradovScheduledMargin
noncomputable section
open Filter VinogradovNearOneBudget VinogradovScaleSelection VinogradovHeightSchedule
open ZetaNearOneBudgetLimit (scale scale_pos scale_atTop)
open ZetaNearOneLogProfile (height)
open ZetaVinogradovLocalDisc (profile)
open scoped Topology

/-- The single natural degree used at the actual ordinate. -/
def order (t : ℝ) : ℕ := index (scale t)

/-- A fully specified conservative Vinogradov--Korobov width. -/
def width (t : ℝ) : ℝ :=
  1 / (19327352832 * scale t ^ (2 / 3 : ℝ) * Real.log (scale t) ^ (1 / 3 : ℝ))

/-- All constant terms in the complete two-height reserve. -/
def reserveConstant (K : ℝ) : ℝ :=
  3*K + 2 * Real.log 8192 + Real.log 2 + Real.log 589824 + 20

/-- The entire actual reserve has a uniform second-logarithm majorant. -/
theorem reserve_le (K : ℝ) {t : ℝ} (hL : 1 < scale t) (hl : 1 ≤ Real.log (scale t))
    (hs : 2 ≤ size (scale t)) :
    ZetaVinogradovMargin.reserve K (order t) t ≤ reserveConstant K + 7 * Real.log (scale t) := by
  have hi := (rounding hs).1
  have hg := growth_pos hi
  have hgrowth := growth_mul_le hL hs
  have hdouble := (ZetaLogLogBudget.scale_double_bounds t).2
  have hdoubleLog := Real.log_le_log (scale_pos (2 * t)) hdouble
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (scale_pos t).ne'] at hdoubleLog
  have hgdouble := mul_le_mul_of_nonneg_left hdouble hg.le
  have h1 : profile (order t) t ≤ Real.log 8192 + 2 * Real.log (scale t) := by
    change Real.log 8192 + growth (index (scale t)) * scale t + Real.log (scale t) ≤ _
    linarith
  have h2 : profile (order t) (2 * t) ≤
      Real.log 8192 + Real.log 2 + 3 * Real.log (scale t) := by
    change Real.log 8192 + growth (index (scale t)) * scale (2 * t) +
      Real.log (scale (2 * t)) ≤ _
    nlinarith
  have hdelta := log_inverse_delta_le hL.le hl hs
  unfold ZetaVinogradovMargin.reserve reserveConstant
  change _ + _ + _ + Real.log (1 / delta (index (scale t))) + _ ≤ _
  linarith

/-- The displayed width is positive once the second logarithm is positive. -/
theorem width_pos {t : ℝ} (hL : 1 < scale t) : 0 < width t := by
  unfold width
  positivity [Real.log_pos hL, scale_pos t]

/-- Once the fixed constants are paid, the complete proposed classical
width fits inside the already proved actual-zero margin. -/
theorem width_le_margin {K : ℝ} (hK : 0 ≤ K) {t : ℝ} (hL : 1 < scale t) (hl : 1 ≤ Real.log (scale t))
    (hs : 2 ≤ size (scale t)) (hC : reserveConstant K ≤ Real.log (scale t)) :
    width t ≤ ZetaVinogradovMargin.width K (order t) t := by
  have hlog := Real.log_pos hL
  have hQ : ZetaVinogradovMargin.reserve K (order t) t ≤ 8 * Real.log (scale t) := by
    linarith [reserve_le K hL hl hs]
  have hQpos : 0 < ZetaVinogradovMargin.reserve K (order t) t := by
    have h : 20 ≤ ZetaVinogradovMargin.reserve K (order t) t :=
      (ZetaVinogradovMargin.reserve_bounds hK (rounding hs).1 t).1
    linarith
  have hδ := delta_pos (order t)
  have hden : 4096 * ZetaVinogradovMargin.reserve K (order t) t / delta (order t) ≤
      19327352832 * scale t ^ (2 / 3 : ℝ) * Real.log (scale t) ^ (1 / 3 : ℝ) := by
    have hi := inverse_delta_le hs
    calc
      _ = 4096 * ZetaVinogradovMargin.reserve K (order t) t * (1 / delta (order t)) := by ring
      _ ≤ (4096 * (8 * Real.log (scale t))) * (589824 * size (scale t) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hQ (by norm_num)) hi
          (by positivity) (by positivity)
      _ = 19327352832 * (size (scale t) ^ 2 * Real.log (scale t)) := by ring
      _ = _ := by rw [balanced_identity hL]; ring
  have h := one_div_le_one_div_of_le
    (by positivity : 0 < 4096 * ZetaVinogradovMargin.reserve K (order t) t / delta (order t)) hden
  simpa only [width, ZetaVinogradovMargin.width, one_div_div] using h

/-- The original starting height, including the unit local-disc buffer,
is eventually paid by the same growing degree at the actual ordinate. -/
theorem eventually_parameters {K : ℝ} (hK : 0 ≤ K) : ∀ᶠ t : ℝ in atTop,
    12 ≤ order t ∧ (heightThreshold (order t) : ℝ) + 1 ≤ t ∧
      0 < width t ∧ width t ≤ ZetaVinogradovMargin.width K (order t) t := by
  have hready := scale_atTop.eventually eventually_threshold
  filter_upwards [hready, eventually_ge_atTop (4 : ℝ),
    scale_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    scale_atTop.eventually (eventually_ge_atTop (2 * Real.log 2)),
    (Real.tendsto_log_atTop.comp scale_atTop).eventually
      (eventually_ge_atTop (reserveConstant K))] with t ht ht4 hL hL2 hC
  obtain ⟨hi, hl, hs, hT⟩ := ht
  refine ⟨hi, ?_, width_pos hL, width_le_margin hK hL hl hs hC⟩
  have hexp : Real.exp (scale t / 2) ≤ (t + 2) / 2 := by
    have h := Real.exp_le_exp.mpr (show scale t / 2 ≤ scale t - Real.log 2 by linarith)
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
    have he : Real.exp (scale t) = t + 2 := by
      simp only [scale, height, abs_of_nonneg (by linarith : 0 ≤ t),
        Real.exp_log (by linarith : 0 < t + 2)]
    rwa [he] at h
  change (heightThreshold (order t) : ℝ) ≤ _ at hT
  linarith

/-- Reflection leaves both the actual natural degree and the displayed
classical width unchanged. -/
theorem abs_invariance (t : ℝ) : order |t| = order t ∧ width |t| = width t := by
  simp [order, width, scale, height]

end
end RiemannGaussian.ZetaVinogradovScheduledMargin

-- Modified from David Sanftenberg’s RiemannGaussian for the Lean 4.28.0 certificate.
