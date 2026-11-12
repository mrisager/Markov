import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-! Uniform finite spatial windows for smooth compact functions on a pair
of real lines, and the first one-dimensional Poisson step. -/

noncomputable section
open Set MeasureTheory FourierTransform
open scoped ContDiff SchwartzMap
namespace Markov

theorem compact_pair_coordinate_window {f : ℝ × ℝ → ℂ}
    (hf : HasCompactSupport f) :
    ∃ (R : ℝ) (N : Finset ℤ), 0 < R ∧
      (∀ n : ℤ, n ∉ N → ∀ y : ℝ, f (n, y) = 0) ∧
      (∀ x y : ℝ, y ∉ Icc (-R) R → f (x, y) = 0) := by
  obtain ⟨R, hR, hsub⟩ := hf.isBounded.subset_closedBall_lt 0 (0 : ℝ × ℝ)
  have hb (x y : ℝ) (hxy : f (x, y) ≠ 0) : |x| ≤ R ∧ |y| ≤ R := by
    have hm : (x, y) ∈ tsupport f := subset_closure hxy
    have hh := hsub hm
    simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def,
      Real.norm_eq_abs, max_le_iff] using hh
  refine ⟨R, Finset.Icc ⌊-R⌋ ⌈R⌉, hR, ?_, ?_⟩
  · intro n hn y
    by_contra hny
    have hnR := (hb n y hny).1
    apply hn
    apply Finset.mem_Icc.mpr
    have hlow : (⌊-R⌋ : ℝ) ≤ n := (Int.floor_le _).trans (abs_le.mp hnR).1
    have hhigh : (n : ℝ) ≤ ⌈R⌉ := (abs_le.mp hnR).2.trans (Int.le_ceil _)
    exact ⟨by exact_mod_cast hlow, by exact_mod_cast hhigh⟩
  · intro x y hy
    by_contra hxy
    exact hy (abs_le.mp (hb x y hxy).2)

def compactPairPeriodization (f : ℝ × ℝ → ℂ) (N : Finset ℤ) (y : ℝ) : ℂ :=
  ∑ n ∈ N, f (n, y)

theorem compactPairPeriodization_contDiff (f : ℝ × ℝ → ℂ) (N : Finset ℤ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (compactPairPeriodization f N) := by
  apply ContDiff.sum
  intro n hn
  exact hf.comp (contDiff_const.prodMk contDiff_id)

theorem compactPairPeriodization_hasCompactSupport (f : ℝ × ℝ → ℂ) (N : Finset ℤ)
    (hf : HasCompactSupport f) : HasCompactSupport (compactPairPeriodization f N) := by
  obtain ⟨R, _M, _hR, _hfirst, hsecond⟩ := compact_pair_coordinate_window hf
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-R) R))
  intro y hy
  exact Finset.sum_eq_zero (fun n _ => hsecond n y hy)

theorem compact_pair_periodization_poisson (f : ℝ × ℝ → ℂ) (N : Finset ℤ)
    (hc : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    (∑' n : ℤ, compactPairPeriodization f N n) =
      ∑' m : ℤ, 𝓕 (compactPairPeriodization f N) m := by
  let g := (compactPairPeriodization_hasCompactSupport f N hs).toSchwartzMap
    (compactPairPeriodization_contDiff f N hc)
  have hg := SchwartzMap.tsum_eq_tsum_fourier g 0
  simpa [g, fourier_eval_zero] using hg

theorem compact_pair_slice_integrable (f : ℝ × ℝ → ℂ) (n : ℤ)
    (hc : Continuous f) (hs : HasCompactSupport f) :
    Integrable (fun y : ℝ => f (n, y)) := by
  apply (hc.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
  have heq : (f ∘ fun y : ℝ => ((n : ℝ), y)) = compactPairPeriodization f {n} := by
    funext y
    simp [compactPairPeriodization]
  change HasCompactSupport (f ∘ fun y : ℝ => ((n : ℝ), y))
  rw [heq]
  exact compactPairPeriodization_hasCompactSupport f {n} hs

theorem compact_pair_periodization_fourier (f : ℝ × ℝ → ℂ) (N : Finset ℤ)
    (hc : Continuous f) (hs : HasCompactSupport f) (m : ℝ) :
    𝓕 (compactPairPeriodization f N) m =
      ∑ n ∈ N, 𝓕 (fun y : ℝ => f (n, y)) m := by
  rw [Real.fourier_eq]
  simp_rw [compactPairPeriodization, Finset.smul_sum]
  rw [integral_finset_sum N (fun n _ =>
    (Real.fourierIntegral_convergent_iff m).mpr (compact_pair_slice_integrable f n hc hs))]
  rfl

end Markov
