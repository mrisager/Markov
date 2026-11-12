import Markov.CompactPairPeriodization
import Markov.PartialFourierPlane
import Markov.SchwartzLatticeSummability

/-! Two-dimensional lattice Poisson for compactly supported Schwartz
functions, by two applications of the pinned one-dimensional theorem. -/

noncomputable section
open Set MeasureTheory FourierTransform
open scoped ContDiff SchwartzMap
namespace Markov

set_option maxHeartbeats 2000000

theorem compact_schwartz_plane_poisson
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hs : HasCompactSupport f) :
    (∑' n : ℤ × ℤ, f (euclideanIntDirection n)) =
      ∑' n : ℤ × ℤ, 𝓕 (f : EuclideanSpace ℝ (Fin 2) → ℂ) (euclideanIntDirection n) := by
  let F : ℝ × ℝ → ℂ := f ∘ euclideanPairEquiv
  have hFc : Continuous F := f.continuous.comp euclideanPairEquiv_continuous
  have hFd : ContDiff ℝ ∞ F := (f.smooth ⊤).comp euclideanPairEquiv_contDiff
  have hFs : HasCompactSupport F := hasCompactSupport_comp_euclideanPairEquiv hs
  obtain ⟨_R, N, _hR, hfirst, _hsecond⟩ := compact_pair_coordinate_window hFs
  let g := compactPairPeriodization F N
  have hfull := schwartz_lattice_summable f
  have hfreq := schwartz_fourier_lattice_summable f
  have hspatial : (∑' n : ℤ × ℤ, f (euclideanIntDirection n)) = ∑' m : ℤ, g m := by
    calc
      _ = ∑' n : ℤ, ∑' m : ℤ, f (euclideanIntDirection (n, m)) := hfull.tsum_prod
      _ = ∑' m : ℤ, ∑' n : ℤ, f (euclideanIntDirection (n, m)) := hfull.tsum_comm.symm
      _ = _ := by
        apply tsum_congr
        intro m
        change (∑' n : ℤ, f (euclideanIntDirection (n, m))) =
          ∑ n ∈ N, F (n, m)
        simp_rw [show ∀ n : ℤ, F (n, m) = f (euclideanIntDirection (n, m)) from
          fun n => rfl]
        apply tsum_eq_sum
        intro n hn
        exact hfirst n hn m
  have hghat (m : ℤ) : 𝓕 g m = ∑ n ∈ N, partialFourierPlane f m n := by
    rw [compact_pair_periodization_fourier F N hFc hFs]
    apply Finset.sum_congr rfl
    intro n _hn
    rw [Real.fourier_real_eq]
    rfl
  have hout (m n : ℤ) (hn : n ∉ N) : partialFourierPlane f m n = 0 := by
    have hz (y : ℝ) : f (euclideanPairEquiv ((n : ℝ), y)) = 0 := hfirst n hn y
    simp only [partialFourierPlane, hz, smul_zero, integral_zero]
  have hpartial (m : ℤ) : (∑' n : ℤ, partialFourierPlane f m n) =
      ∑' k : ℤ, 𝓕 (f : EuclideanSpace ℝ (Fin 2) → ℂ)
        (euclideanIntDirection (k, m)) := by
    have hrow := hfreq.prod_symm.prod_factor m
    have hsample : Summable (fun k : ℤ => 𝓕 (partialFourierPlane f m) k) := by
      simpa only [partialFourierPlane_fourier f.continuous hs, euclideanPairEquiv_int] using hrow
    have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
      (partialFourierPlane_continuous f.continuous hs m)
      (b := 2) (by norm_num) (partialFourierPlane_isBigO hs m) hsample 0
    simpa [fourier_eval_zero, partialFourierPlane_fourier f.continuous hs,
      euclideanPairEquiv_int] using hp
  calc
    _ = ∑' m : ℤ, g m := hspatial
    _ = ∑' m : ℤ, 𝓕 g m := compact_pair_periodization_poisson F N hFd hFs
    _ = ∑' m : ℤ, ∑ n ∈ N, partialFourierPlane f m n := tsum_congr hghat
    _ = ∑' m : ℤ, ∑' n : ℤ, partialFourierPlane f m n := by
      apply tsum_congr
      intro m
      exact (tsum_eq_sum (hout m)).symm
    _ = ∑' m : ℤ, ∑' k : ℤ, 𝓕 (f : EuclideanSpace ℝ (Fin 2) → ℂ)
        (euclideanIntDirection (k, m)) := tsum_congr hpartial
    _ = ∑' k : ℤ, ∑' m : ℤ, 𝓕 (f : EuclideanSpace ℝ (Fin 2) → ℂ)
        (euclideanIntDirection (k, m)) := hfreq.tsum_comm
    _ = _ := hfreq.tsum_prod.symm

end Markov
