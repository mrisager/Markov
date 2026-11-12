import Markov.LogarithmicCountingGrowth
import Markov.FiniteCountingIntegral

/-! Summation by parts for a finite family with a uniform logarithmic
counting estimate. The counting integral makes the inverse-square-root
weight summable uniformly in the upper cutoff. -/

noncomputable section
namespace Markov

/-- A logarithmic-square counting bound gives a uniform bound for the
inverse-square-root weighted sum over the whole finite family. -/
theorem finite_sum_inv_sqrt_le_of_count_log_square
    {ι : Type*} (S : Finset ι) (r : ι → ℝ) (C : ℝ)
    (hr : ∀ i ∈ S, 1 ≤ r i) (hC : 0 ≤ C)
    (hcount : ∀ T : ℝ, 1 ≤ T →
      ((S.filter (fun i => r i ≤ T)).card : ℝ) ≤ C * Real.log (2 * T) ^ 2) :
    ∑ i ∈ S, 1 / Real.sqrt (r i) ≤ 256 * C := by
  have h := finite_sum_inv_sqrt_le_of_count_quarter_rpow S r (128 * C)
    hr (by positivity) (fun T hT =>
      le_quarter_power_of_le_log_square _ C T hC hT (hcount T hT))
  linarith

/-- The same uniform estimate for a nonnegative weight pointwise bounded
by a constant times the inverse square root. -/
theorem finite_sum_le_of_count_log_square
    {ι : Type*} (S : Finset ι) (r w : ι → ℝ) (C L : ℝ)
    (hr : ∀ i ∈ S, 1 ≤ r i) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hcount : ∀ T : ℝ, 1 ≤ T →
      ((S.filter (fun i => r i ≤ T)).card : ℝ) ≤ C * Real.log (2 * T) ^ 2)
    (hw : ∀ i ∈ S, w i ≤ L / Real.sqrt (r i)) :
    ∑ i ∈ S, w i ≤ (256 * C) * L := by
  calc
    ∑ i ∈ S, w i ≤ ∑ i ∈ S, L / Real.sqrt (r i) := Finset.sum_le_sum hw
    _ = L * ∑ i ∈ S, 1 / Real.sqrt (r i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ L * (256 * C) := mul_le_mul_of_nonneg_left
      (finite_sum_inv_sqrt_le_of_count_log_square S r C hr hC hcount) hL
    _ = _ := by ring

end Markov
