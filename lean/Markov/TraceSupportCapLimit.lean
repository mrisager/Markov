import Markov.TraceStrictConvexity
import Markov.TraceConvexCap

/-! Quantitative localization of near-support points on the compact actual
trace body, and vanishing diameter of caps as their depth tends to zero. -/

noncomputable section
open Set Filter
open scoped Topology

namespace Markov

/-- Points whose support value is sufficiently close to the maximum lie
arbitrarily close to the unique actual support point. -/
theorem traceEuclideanBall_near_support_localization
    {n p : EuclideanSpace ℝ (Fin 2)} (hn : n ≠ 0)
    (hp : p ∈ traceEuclideanBall) (hpmax : inner ℝ p n = traceEuclideanSupportHeight n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ traceEuclideanBall,
      traceEuclideanSupportHeight n - δ ≤ inner ℝ x n → dist x p < ε := by
  let K : Set (EuclideanSpace ℝ (Fin 2)) :=
    traceEuclideanBall ∩ {x | ε ≤ dist x p}
  have hK : IsCompact K := isCompact_traceEuclideanBall.inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  by_cases hKne : K.Nonempty
  · obtain ⟨q, hq, hqmax⟩ := hK.exists_isMaxOn hKne
      (show Continuous (fun x : EuclideanSpace ℝ (Fin 2) ↦ inner ℝ x n) from
        continuous_id.inner continuous_const).continuousOn
    have hq_lt : inner ℝ q n < traceEuclideanSupportHeight n := by
      apply lt_of_le_of_ne (inner_le_traceEuclideanSupportHeight n q hq.1)
      intro heq
      have hqp : q = p := (traceEuclideanSupportHeight_exists_unique n hn).unique
        ⟨hq.1, heq⟩ ⟨hp, hpmax⟩
      have hdist : ε ≤ 0 := by simpa only [Set.mem_setOf_eq, hqp, dist_self] using hq.2
      linarith
    refine ⟨(traceEuclideanSupportHeight n - inner ℝ q n) / 2, by linarith, ?_⟩
    intro x hx hnear
    by_contra hdist
    have hxK : x ∈ K := ⟨hx, le_of_not_gt hdist⟩
    have hbound : inner ℝ x n ≤ inner ℝ q n := hqmax hxK
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx _
    by_contra hdist
    exact hKne ⟨x, hx, le_of_not_gt hdist⟩

/-- Every sufficiently shallow actual cap lies in any prescribed ball
around its unique supporting point. Smaller depths satisfy the same bound. -/
theorem traceConvexCap_subset_ball_of_depth_le
    {n p : EuclideanSpace ℝ (Fin 2)} (hn : n ≠ 0)
    (hp : p ∈ traceEuclideanBall) (hpmax : inner ℝ p n = traceEuclideanSupportHeight n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℝ, d ≤ δ → traceConvexCap n d ⊆ Metric.ball p ε := by
  obtain ⟨δ, hδ, hclose⟩ := traceEuclideanBall_near_support_localization hn hp hpmax hε
  refine ⟨δ, hδ, ?_⟩
  intro d hd x hx
  exact hclose x hx.1 (by linarith [hx.2])

/-- The diameter of a sufficiently shallow actual cap is arbitrarily small. -/
theorem traceConvexCap_diam_small
    {n : EuclideanSpace ℝ (Fin 2)} (hn : n ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℝ, d ≤ δ → Metric.diam (traceConvexCap n d) ≤ ε := by
  obtain ⟨p, hp, hpmax⟩ := traceEuclideanSupportHeight_exists_mem n
  obtain ⟨δ, hδ, hclose⟩ := traceConvexCap_subset_ball_of_depth_le hn hp hpmax
    (show 0 < ε / 2 by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro d hd
  apply Metric.diam_le_of_forall_dist_le hε.le
  intro x hx y hy
  have hxp : dist x p < ε / 2 := hclose d hd hx
  have hyp : dist y p < ε / 2 := hclose d hd hy
  have ht := dist_triangle x p y
  rw [dist_comm p y] at ht
  linarith

/-- As the actual cap depth approaches zero from above, its diameter tends to zero. -/
theorem traceConvexCap_diam_tendsto_zero
    {n : EuclideanSpace ℝ (Fin 2)} (hn : n ≠ 0) :
    Tendsto (fun d : ℝ ↦ Metric.diam (traceConvexCap n d)) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := traceConvexCap_diam_small hn (show 0 < ε / 2 by linarith)
  filter_upwards [show ∀ᶠ d : ℝ in 𝓝[>] 0, d < δ from
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with d hd
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.diam_nonneg]
  exact (hsmall d hd.le).trans_lt (by linarith)

end Markov
