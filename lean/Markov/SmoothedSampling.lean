import Mathlib.Analysis.Convolution
import Mathlib.Tactic

/-! Sampling a compact convolution: a uniform finite window justifies the
sum/integral exchange, after which a uniform shifted sampling bound is
averaged against a nonnegative unit-mass kernel. -/

noncomputable section
open Set MeasureTheory
open scoped Convolution
namespace Markov

theorem compact_shifted_sampling_window {f w : ℝ → ℝ}
    (hf : HasCompactSupport f) (hw : HasCompactSupport w) {h : ℝ} (hh : 0 < h) :
    ∃ N : Finset ℤ, ∀ u : ℝ, w u ≠ 0 → ∀ n : ℤ, n ∉ N → f (h * n - u) = 0 := by
  obtain ⟨R, _hR, hRf⟩ := hf.isBounded.subset_closedBall_lt 0 (0 : ℝ)
  obtain ⟨T, _hT, hTw⟩ := hw.isBounded.subset_closedBall_lt 0 (0 : ℝ)
  refine ⟨Finset.Icc ⌊-((R + T) / h)⌋ ⌈(R + T) / h⌉, ?_⟩
  intro u hu n hn
  by_contra hfn
  have hfu : |h * (n : ℝ) - u| ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using
      hRf (subset_closure hfn)
  have hwu : |u| ≤ T := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using
      hTw (subset_closure hu)
  have hnorm : h * |(n : ℝ)| ≤ R + T := by
    have ha := abs_add_le (h * (n : ℝ) - u) u
    rw [sub_add_cancel, abs_mul, abs_of_pos hh] at ha
    linarith
  have hnreal : |(n : ℝ)| ≤ (R + T) / h :=
    (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hnorm)
  apply hn
  apply Finset.mem_Icc.mpr
  have hlo : (⌊-((R + T) / h)⌋ : ℝ) ≤ n :=
    (Int.floor_le _).trans (abs_le.mp hnreal).1
  have hhi : (n : ℝ) ≤ ⌈(R + T) / h⌉ :=
    (abs_le.mp hnreal).2.trans (Int.le_ceil _)
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

theorem smoothed_sampling_bound (f w : ℝ → ℝ)
    (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hwc : Continuous w) (hws : HasCompactSupport w)
    (hwn : ∀ u, 0 ≤ w u) (hwm : ∫ u, w u = 1)
    {h C : ℝ} (hh : 0 < h)
    (hsample : ∀ u : ℝ, |h * (∑' n : ℤ, f (h * n - u)) - ∫ x, f x| ≤ C) :
    Summable (fun n : ℤ => (w ⋆ f) (h * n)) ∧
      |h * (∑' n : ℤ, (w ⋆ f) (h * n)) - ∫ x, f x| ≤ C := by
  obtain ⟨N, hN⟩ := compact_shifted_sampling_window hfs hws hh
  have hi (n : ℤ) : Integrable (fun u : ℝ => w u * f (h * n - u)) :=
    (hwc.mul (hfc.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hws.mul_right
  have hzero (n : ℤ) (hn : n ∉ N) : (w ⋆ f) (h * n) = 0 := by
    change (∫ u, w u * f (h * n - u)) = 0
    apply integral_eq_zero_of_ae
    filter_upwards with u
    change w u * f (h * n - u) = 0
    by_cases hu : w u = 0
    · rw [hu, zero_mul]
    · rw [hN u hu n hn, mul_zero]
  have hsum : HasSum (fun n : ℤ => (w ⋆ f) (h * n))
      (∑ n ∈ N, (w ⋆ f) (h * n)) := hasSum_sum_of_ne_finset_zero hzero
  refine ⟨hsum.summable, ?_⟩
  let P : ℝ → ℝ := fun u => h * (∑ n ∈ N, f (h * n - u)) - ∫ x, f x
  have hP : Continuous P := by
    have hc : Continuous (fun u : ℝ => ∑ n ∈ N, f (h * n - u)) := by
      apply continuous_finset_sum
      intro n _hn
      exact hfc.comp (continuous_const.sub continuous_id)
    exact (continuous_const.mul hc).sub continuous_const
  have hwP : Integrable (fun u => w u * P u) :=
    (hwc.mul hP).integrable_of_hasCompactSupport hws.mul_right
  have hwI : Integrable w := hwc.integrable_of_hasCompactSupport hws
  have hb (u : ℝ) : |w u * P u| ≤ w u * C := by
    by_cases hu : w u = 0
    · simp only [hu, zero_mul, abs_zero, le_refl]
    · have heq : (∑' n : ℤ, f (h * n - u)) = ∑ n ∈ N, f (h * n - u) :=
        tsum_eq_sum (fun n hn => hN u hu n hn)
      have hs := hsample u
      rw [heq] at hs
      rw [abs_mul, abs_of_nonneg (hwn u)]
      exact mul_le_mul_of_nonneg_left hs (hwn u)
  have hid : h * (∑' n : ℤ, (w ⋆ f) (h * n)) - (∫ x, f x) = ∫ u, w u * P u := by
    rw [hsum.tsum_eq]
    have heq : (fun u => w u * P u) =
        (fun u => h * (∑ n ∈ N, w u * f (h * n - u)) - w u * ∫ x, f x) := by
      funext u
      dsimp [P]
      rw [← Finset.mul_sum]
      ring
    rw [heq, integral_sub ((integrable_finset_sum N (fun n _ => hi n)).const_mul h)
      (hwI.mul_const _), integral_const_mul, integral_finset_sum N (fun n _ => hi n),
      integral_mul_const, hwm, one_mul]
    rfl
  rw [hid]
  calc
    _ = ‖∫ u, w u * P u‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ u, ‖w u * P u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u, w u * C := integral_mono hwP.norm (hwI.mul_const C)
      (fun u => by simpa only [Real.norm_eq_abs] using hb u)
    _ = C := by rw [integral_mul_const, hwm, one_mul]

end Markov
