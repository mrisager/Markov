import Markov.TraceSectionConcavity
import Markov.TraceSectionFourier
import Markov.ConcaveSamplingRescale

/-! The coefficient-seven sampling estimate applied to the actual trace-body
section profile, with its integral identified with Euclidean area. -/

noncomputable section
open Set MeasureTheory

namespace Markov

/-- Every unit direction has support height at least the actual Euclidean inradius. -/
theorem traceEuclideanInradius_le_supportHeight
    {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) :
    traceEuclideanInradius ≤ traceEuclideanSupportHeight θ := by
  have hp : traceEuclideanInradius • θ ∈ traceEuclideanBall := by
    apply closedBall_subset_traceEuclideanBall
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos traceEuclideanInradius_pos, hθ, mul_one, le_refl]
  have hi := inner_le_traceEuclideanSupportHeight θ (traceEuclideanInradius • θ) hp
  simpa only [real_inner_smul_left, real_inner_self_eq_norm_sq, hθ, one_pow, mul_one] using hi

/-- The actual support interval of every unit-normal section has positive length. -/
theorem traceSection_support_interval_lt
    {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) :
    -traceEuclideanSupportHeight (-θ) < traceEuclideanSupportHeight θ := by
  have hp := traceEuclideanInradius_le_supportHeight hθ
  have hm := traceEuclideanInradius_le_supportHeight (show ‖-θ‖ = 1 by simpa using hθ)
  linarith [traceEuclideanInradius_pos]

/-- Lemma 9 for actual trace-body sections. The sampled series is absolutely
finite-supported, and its integral main term is exactly the actual Euclidean area. -/
theorem traceSectionProfile_sampling
    {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1) {h : ℝ} (hh : 0 < h)
    (hhsmall : h < (traceEuclideanSupportHeight θ + traceEuclideanSupportHeight (-θ)) / 8)
    (y : ℝ) :
    Summable (fun n : ℤ ↦ traceSectionProfile θ (h * ((n : ℝ) + y))) ∧
      |h * (∑' n : ℤ, traceSectionProfile θ (h * ((n : ℝ) + y))) - traceEuclideanArea| ≤
        7 * h * (traceSectionProfile θ (-traceEuclideanSupportHeight (-θ) + h) +
          traceSectionProfile θ (traceEuclideanSupportHeight θ - h)) := by
  have key := concave_sampling_interval_with_summability
    (traceSection_support_interval_lt hθ) (continuous_traceSectionProfile hθ)
    (concaveOn_traceSectionProfile hθ)
    (fun x hx ↦ traceSectionProfile_eq_zero_of_outside_support hθ hx)
    hh (by simpa only [sub_neg_eq_add] using hhsmall) y
  rw [traceSectionProfile_integral hθ] at key
  exact key

end Markov
