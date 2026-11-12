import T1MertensEnvelope
import Mathlib.Algebra.BigOperators.Intervals

/-! Exact discrete partial summation for the actual summatory Möbius
function. Its envelope remains the genuine supremum, not a cancellation input. -/
noncomputable section
open Classical Finset
open scoped ArithmeticFunction.Moebius
namespace Markov

theorem t1_mertensNat_succ (n : ℕ) :
    t1_mertensNat (n + 1) = t1_mertensNat n + μ (n + 1) := by
  unfold t1_mertensNat
  exact Finset.sum_Icc_succ_top (by omega) _

theorem t1_moebius_square_abel (D N : ℕ) (hDN : D ≤ N) :
    (∑ g ∈ Finset.Ioc D N, (μ g : ℝ) / (g : ℝ)^2) =
      (t1_mertensNat N : ℝ) / (N : ℝ)^2 -
      (t1_mertensNat D : ℝ) / (D : ℝ)^2 +
      ∑ g ∈ Finset.Ico D N, (t1_mertensNat g : ℝ) *
        (1 / (g : ℝ)^2 - 1 / ((g : ℝ) + 1)^2) := by
  induction N, hDN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top hn, Finset.sum_Ico_succ_top hn, ih,
      t1_mertensNat_succ]
    push_cast
    ring

theorem t1_square_abel_kernel_nonneg (x : ℝ) (hx : 0 < x) :
    0 ≤ 1 / x^2 - 1 / (x + 1)^2 := by
  have hsq : x^2 ≤ (x+1)^2 := by nlinarith
  exact sub_nonneg.mpr (one_div_le_one_div_of_le (sq_pos_of_pos hx) hsq)

theorem t1_square_abel_kernel_bound (x : ℝ) (hx : 0 < x) :
    x * (1 / x^2 - 1 / (x + 1)^2) ≤ 2 * (1 / x - 1 / (x + 1)) := by
  have hx0 := ne_of_gt hx
  have hx10 : x + 1 ≠ 0 := by linarith
  have hid : 2 * (1 / x - 1 / (x+1)) -
      x * (1 / x^2 - 1 / (x+1)^2) = 1 / (x * (x+1)^2) := by
    field_simp
    ring
  have hpos : 0 ≤ 1 / (x * (x+1)^2) := by positivity
  linarith

theorem t1_reciprocal_interval_telescope (D N : ℕ) (hDN : D ≤ N) :
    (∑ g ∈ Finset.Ico D N, (1 / (g : ℝ) - 1 / ((g : ℝ)+1))) =
      1 / (D : ℝ) - 1 / (N : ℝ) := by
  induction N, hDN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih]
    push_cast
    ring

end Markov
