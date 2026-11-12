import Markov.NormalDeterminant
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-! Absolute convergence of Schwartz samples on the full standard integer
lattice, including Fourier samples, with justified row sums and reindexing. -/

noncomputable section
open FourierTransform
open scoped FourierTransform

namespace Markov

/-- A summable product weight for each integer coordinate, including zero. -/
theorem summable_integer_quadratic_weight :
    Summable (fun n : ℤ ↦ 1 / (1 + (n : ℝ) ^ 2)) := by
  have hp : Summable (fun n : ℤ ↦ 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  apply hp.of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (1 + (n : ℝ) ^ 2))]
  exact one_div_le_one_div_of_le (sq_pos_of_ne_zero hnR) (by linarith)

private theorem integer_direction_norm_sq (n : ℤ × ℤ) :
    ‖euclideanIntDirection n‖ ^ 2 = (n.1 : ℝ) ^ 2 + (n.2 : ℝ) ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, euclideanIntDirection, Fin.sum_univ_two,
    Real.norm_eq_abs]

/-- The zeroth, second, and fourth Schwartz seminorms give a separated
summable weight in the two integer coordinates. -/
theorem schwartz_lattice_product_weight_bound
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (n : ℤ × ℤ) :
    ‖f (euclideanIntDirection n)‖ ≤
      ((SchwartzMap.seminorm ℂ 0 0) f + (SchwartzMap.seminorm ℂ 2 0) f +
        (SchwartzMap.seminorm ℂ 4 0) f) /
          (1 + (n.1 : ℝ) ^ 2) / (1 + (n.2 : ℝ) ^ 2) := by
  have h0 := SchwartzMap.norm_le_seminorm ℂ f (euclideanIntDirection n)
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℂ f 2 (euclideanIntDirection n)
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℂ f 4 (euclideanIntDirection n)
  have hs := integer_direction_norm_sq n
  have hfour : ‖euclideanIntDirection n‖ ^ 4 =
      ((n.1 : ℝ) ^ 2 + (n.2 : ℝ) ^ 2) ^ 2 := by nlinarith [sq_nonneg (‖euclideanIntDirection n‖ ^ 2)]
  rw [hs] at h2
  rw [hfour] at h4
  have hcross : (n.1 : ℝ) ^ 2 * (n.2 : ℝ) ^ 2 ≤
      ((n.1 : ℝ) ^ 2 + (n.2 : ℝ) ^ 2) ^ 2 := by
    nlinarith [sq_nonneg ((n.1 : ℝ) ^ 2 - (n.2 : ℝ) ^ 2)]
  have hmul := mul_le_mul_of_nonneg_right hcross (norm_nonneg (f (euclideanIntDirection n)))
  apply (le_div_iff₀ (by positivity : 0 < 1 + (n.2 : ℝ) ^ 2)).2
  apply (le_div_iff₀ (by positivity : 0 < 1 + (n.1 : ℝ) ^ 2)).2
  nlinarith

/-- Samples of a Schwartz function on the full integer plane converge absolutely. -/
theorem schwartz_lattice_norm_summable
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    Summable (fun n : ℤ × ℤ ↦ ‖f (euclideanIntDirection n)‖) := by
  let C := (SchwartzMap.seminorm ℂ 0 0) f + (SchwartzMap.seminorm ℂ 2 0) f +
    (SchwartzMap.seminorm ℂ 4 0) f
  have hw := summable_integer_quadratic_weight.mul_of_nonneg
    summable_integer_quadratic_weight (fun _ ↦ by positivity) (fun _ ↦ by positivity)
  apply (hw.mul_left C).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro n
  simpa only [C, one_div, div_eq_mul_inv, mul_assoc, one_mul] using
    schwartz_lattice_product_weight_bound f n

/-- In particular, the complex lattice sum itself converges. -/
theorem schwartz_lattice_summable
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    Summable (fun n : ℤ × ℤ ↦ f (euclideanIntDirection n)) :=
  (schwartz_lattice_norm_summable f).of_norm

/-- Every row of lattice samples converges absolutely. -/
theorem schwartz_lattice_row_norm_summable
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (n : ℤ) :
    Summable (fun m : ℤ ↦ ‖f (euclideanIntDirection (n, m))‖) :=
  (schwartz_lattice_norm_summable f).prod_factor n

/-- Every row of complex samples converges. -/
theorem schwartz_lattice_row_summable
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (n : ℤ) :
    Summable (fun m : ℤ ↦ f (euclideanIntDirection (n, m))) :=
  (schwartz_lattice_summable f).prod_factor n

/-- Absolute convergence justifies the two iterated integer sums. -/
theorem schwartz_lattice_tsum_prod
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    (∑' n : ℤ × ℤ, f (euclideanIntDirection n)) =
      ∑' n : ℤ, ∑' m : ℤ, f (euclideanIntDirection (n, m)) :=
  (schwartz_lattice_summable f).tsum_prod

/-- Fourier samples of a Schwartz function converge absolutely on the full lattice. -/
theorem schwartz_fourier_lattice_norm_summable
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    Summable (fun n : ℤ × ℤ ↦ ‖𝓕 (f : EuclideanSpace ℝ (Fin 2) → ℂ)
      (euclideanIntDirection n)‖) :=
  schwartz_lattice_norm_summable (𝓕 f)

/-- The full complex Fourier lattice sum converges. -/
theorem schwartz_fourier_lattice_summable
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    Summable (fun n : ℤ × ℤ ↦ 𝓕 (f : EuclideanSpace ℝ (Fin 2) → ℂ)
      (euclideanIntDirection n)) :=
  (schwartz_fourier_lattice_norm_summable f).of_norm

/-- Absolute convergence is retained under any bijective relabelling of the lattice. -/
theorem schwartz_lattice_reindex_norm_summable {ι : Type*}
    (e : ι ≃ (ℤ × ℤ)) (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    Summable (fun i : ι ↦ ‖f (euclideanIntDirection (e i))‖) :=
  (schwartz_lattice_norm_summable f).comp_injective e.injective

/-- A bijective relabelling preserves the absolutely convergent lattice sum. -/
theorem schwartz_lattice_tsum_reindex {ι : Type*}
    (e : ι ≃ (ℤ × ℤ)) (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    (∑' i : ι, f (euclideanIntDirection (e i))) =
      ∑' n : ℤ × ℤ, f (euclideanIntDirection n) :=
  e.tsum_eq (fun n ↦ f (euclideanIntDirection n))

end Markov
