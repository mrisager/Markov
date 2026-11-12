import Markov.LogarithmicCountingGrowth

/-! The paper's splitting radius `H * sqrt H = H^(3/2)` satisfies the
logarithmic restriction of weighted estimate (83) above a fixed threshold. -/

namespace Markov

/-- An explicit sufficiently-large-height version of the logarithmic
condition at the splitting radius in Corollary 11. -/
theorem corollary11_split_log_cutoff (D H : ℝ) (hD : 0 ≤ D)
    (hH : 1 ≤ H) (hlarge : (4 * D + 1) ^ 2 ≤ H) :
    D * Real.log (2 * (H * Real.sqrt H)) ≤ H := by
  have hHpos : 0 < H := by linarith
  have hs : 0 ≤ Real.sqrt H := Real.sqrt_nonneg H
  have hsquare : Real.sqrt H ^ 2 = H := Real.sq_sqrt hHpos.le
  have hslarge : 4 * D + 1 ≤ Real.sqrt H := by
    nlinarith
  have hsone : 1 ≤ Real.sqrt H := by linarith
  have hlog : Real.log H ≤ 2 * Real.sqrt H := by
    have hh := Real.log_le_rpow_div hHpos.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at hh
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogsplit : Real.log (2 * (H * Real.sqrt H)) =
      Real.log 2 + (3 / 2 : ℝ) * Real.log H := by
    rw [Real.log_mul (by norm_num) (mul_pos hHpos (Real.sqrt_pos.mpr hHpos)).ne',
      Real.log_mul hHpos.ne' (Real.sqrt_pos.mpr hHpos).ne', Real.log_sqrt hHpos.le]
    ring
  calc
    D * Real.log (2 * (H * Real.sqrt H)) ≤ D * (1 + 3 * Real.sqrt H) := by
      rw [hlogsplit]
      exact mul_le_mul_of_nonneg_left (by linarith) hD
    _ ≤ D * (4 * Real.sqrt H) := mul_le_mul_of_nonneg_left (by linarith) hD
    _ = (4 * D) * Real.sqrt H := by ring
    _ ≤ Real.sqrt H * Real.sqrt H := mul_le_mul_of_nonneg_right (by linarith) hs
    _ = H := by nlinarith [hsquare]

/-- The splitting radius is admissible for the finite large-direction
partial summation whenever the height is at least one. -/
theorem corollary11_split_radius_one_le (H : ℝ) (hH : 1 ≤ H) :
    1 ≤ H * Real.sqrt H := by
  have hs : 1 ≤ Real.sqrt H := (Real.one_le_sqrt).mpr hH
  nlinarith

end Markov
