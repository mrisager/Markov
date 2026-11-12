import Markov.TraceSectionConcavity
import Markov.TraceProjectedMollifier
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Convolution

/-! Central symmetry of the actual trace body, its caps and section
profiles, and evenness of the projected radial smoothing kernel. -/

noncomputable section
open Set MeasureTheory Function
open scoped Pointwise Convolution

namespace Markov

/-- The actual body is centrally symmetric because its gauge is a norm. -/
theorem neg_mem_traceEuclideanBall_iff (x : EuclideanSpace ℝ (Fin 2)) :
    -x ∈ traceEuclideanBall ↔ x ∈ traceEuclideanBall := by
  rw [mem_traceEuclideanBall_iff, mem_traceEuclideanBall_iff]
  simp only [traceEuclideanGauge, map_neg, norm_neg]

theorem neg_traceEuclideanBall : -traceEuclideanBall = traceEuclideanBall := by
  ext x
  simpa only [Set.mem_neg] using neg_mem_traceEuclideanBall_iff x

/-- Opposite normal directions have the same actual support height. -/
theorem traceEuclideanSupportHeight_neg (θ : EuclideanSpace ℝ (Fin 2)) :
    traceEuclideanSupportHeight (-θ) = traceEuclideanSupportHeight θ := by
  have hle (n : EuclideanSpace ℝ (Fin 2)) :
      traceEuclideanSupportHeight (-n) ≤ traceEuclideanSupportHeight n := by
    obtain ⟨p, hp, hpmax⟩ := traceEuclideanSupportHeight_exists_mem (-n)
    have hi := inner_le_traceEuclideanSupportHeight n (-p)
      ((neg_mem_traceEuclideanBall_iff p).mpr hp)
    rw [inner_neg_left, ← inner_neg_right] at hi
    rw [hpmax] at hi
    exact hi
  exact le_antisymm (hle θ) (by simpa only [neg_neg] using hle (-θ))

/-- Opposite caps are exact negatives of each other in the actual body. -/
theorem traceConvexCap_neg_normal (θ : EuclideanSpace ℝ (Fin 2)) (d : ℝ) :
    traceConvexCap (-θ) d = -traceConvexCap θ d := by
  ext x
  simp only [Set.mem_neg, traceConvexCap, Set.mem_setOf_eq,
    traceEuclideanSupportHeight_neg, neg_mem_traceEuclideanBall_iff,
    inner_neg_left, inner_neg_right]

theorem traceConvexCap_diam_neg_normal (θ : EuclideanSpace ℝ (Fin 2)) (d : ℝ) :
    Metric.diam (traceConvexCap (-θ) d) = Metric.diam (traceConvexCap θ d) := by
  rw [traceConvexCap_neg_normal, ← Set.image_neg_eq_neg]
  exact (isometry_neg : Isometry (fun x : EuclideanSpace ℝ (Fin 2) ↦ -x)).diam_image _

/-- The actual length profile is even; reversing the transverse coordinate
preserves one-dimensional Lebesgue measure. -/
theorem traceSectionProfile_even (θ : EuclideanSpace ℝ (Fin 2)) : Function.Even (traceSectionProfile θ) := by
  intro t
  unfold traceSectionProfile
  calc
    _ = ∫ s : ℝ, traceEuclideanBall.indicator (fun _ ↦ (1 : ℝ))
        (traceSectionPoint θ (-t) (-s)) := (integral_neg_eq_self _ volume).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with s
      have hp : traceSectionPoint θ (-t) (-s) = -traceSectionPoint θ t s := by
        dsimp [traceSectionPoint]
        module
      rw [hp]
      classical
      by_cases hs : traceSectionPoint θ t s ∈ traceEuclideanBall
      · simp only [indicator_of_mem hs,
          indicator_of_mem ((neg_mem_traceEuclideanBall_iff _).mpr hs)]
      · simp only [indicator_of_notMem hs,
          indicator_of_notMem (fun hh ↦ hs ((neg_mem_traceEuclideanBall_iff _).mp hh))]

/-- Radiality makes every actual projected smoothing kernel even. -/
theorem traceProjectedMollifier_even (Q : ℝ) (θ : EuclideanSpace ℝ (Fin 2)) :
    Function.Even (traceProjectedMollifier Q θ) := by
  intro t
  unfold traceProjectedMollifier
  calc
    _ = ∫ s : ℝ, traceScaledMollifier Q ((-t) • θ + (-s) • quarterTurnNormal θ) :=
      (integral_neg_eq_self _ volume).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with s
      apply traceScaledMollifier_radial
      have hp : (-t) • θ + (-s) • quarterTurnNormal θ =
          -(t • θ + s • quarterTurnNormal θ) := by module
      rw [hp, norm_neg]

/-- Convolving two even real functions preserves evenness. -/
theorem convolution_even_real {f g : ℝ → ℝ} (hf : Function.Even f) (hg : Function.Even g) :
    Function.Even (f ⋆ g) := by
  intro t
  change (∫ y : ℝ, f y * g (-t - y)) = ∫ y : ℝ, f y * g (t - y)
  calc
    _ = ∫ y : ℝ, f (-y) * g (-t - (-y)) := (integral_neg_eq_self _ volume).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      have hid : -t - (-y) = -(t - y) := by ring
      rw [hf y, hid, hg (t - y)]

end Markov
