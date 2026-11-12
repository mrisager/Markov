import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! The finite telescoping step in v1 Lemma 9. Cell secant bounds are
kept explicit here and are discharged by concavity in the next adapter. -/

noncomputable section
open Set MeasureTheory
namespace Markov

theorem sampling_mesh_core_bounds
    (f : ℝ → ℝ) (x : ℕ → ℝ) (h : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hint : ∀ j ∈ Finset.Ico 1 N, IntervalIntegrable f volume (x j) (x (j + 1)))
    (hcell : ∀ j ∈ Finset.Ico 1 N,
      (h / 2) * (f (x (j + 1)) - f (x j)) ≤
          (∫ t in x j..x (j + 1), f t) - h * f (x j) ∧
      (∫ t in x j..x (j + 1), f t) - h * f (x j) ≤
          (h / 2) * (f (x j) - f (x (j - 1)))) :
    (h / 2) * (f (x N) - f (x 1)) ≤
        (∫ t in x 1..x N, f t) - h * ∑ j ∈ Finset.Ico 1 N, f (x j) ∧
    (∫ t in x 1..x N, f t) - h * ∑ j ∈ Finset.Ico 1 N, f (x j) ≤
        (h / 2) * (f (x (N - 1)) - f (x 0)) := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (f := f) (μ := volume) (a := x) hN
    (fun j hj => hint j (by simpa only [Finset.mem_Ico, Set.mem_Ico] using hj))
  have hdiff : (∑ j ∈ Finset.Ico 1 N,
      ((∫ t in x j..x (j + 1), f t) - h * f (x j))) =
      (∫ t in x 1..x N, f t) - h * ∑ j ∈ Finset.Ico 1 N, f (x j) := by
    rw [Finset.sum_sub_distrib, hsum, Finset.mul_sum]
  have hlo := Finset.sum_le_sum (fun j hj => (hcell j hj).1)
  have hhi := Finset.sum_le_sum (fun j hj => (hcell j hj).2)
  rw [← Finset.mul_sum, Finset.sum_Ico_sub (fun j => f (x j)) hN, hdiff] at hlo
  have htel : (∑ j ∈ Finset.Ico 1 N, (f (x j) - f (x (j - 1)))) =
      f (x (N - 1)) - f (x 0) := by
    simpa only [Nat.add_sub_cancel, Nat.sub_self] using
      (Finset.sum_Ico_sub (fun j => f (x (j - 1))) hN)
  rw [hdiff, ← Finset.mul_sum, htel] at hhi
  exact ⟨hlo, hhi⟩

end Markov
