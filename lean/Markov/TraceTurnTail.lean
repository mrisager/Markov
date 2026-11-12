import Markov.SignedCutoffTurnDecay
import Markov.CutoffTurnSummation
import Markov.TailPolynomialAbsorption
import Markov.TraceCornerEstimate

/-! The complementary-turn tail and two-part estimate of v1
Theorem 2 for the trace norm, using the primitive-height cutoff and
the boundary normal-turn measure. -/

noncomputable section
open Set MeasureTheory

namespace Markov

/-- The entire uncut trace boundary has exponentially small actual turn
at every positive natural cutoff. All component estimates are discharged. -/
theorem traceBoundary_turn_tail_nat :
    ∃ M κ : ℝ, 0 < M ∧ 0 < κ ∧ ∀ H : ℕ, 1 ≤ H →
      (traceBoundaryTurn
        (frontier (Metric.closedBall (0 : TracePlane) 1) \
          (↑(cutoffCorners traceBasis H) : Set TracePlane))).toReal ≤
        M * Real.exp (-(κ * (H : ℝ))) := by
  obtain ⟨D, c, hD, hc, hgap⟩ := signed_cutoff_arc_turn_cutoff_decay
  refine ⟨(72 * D) * (48 / c ^ 3), c / 2, by positivity, by positivity, ?_⟩
  intro H hH
  have hs := traceBoundaryTurn_uncut_le_exp_of_gap_bound H hH D c hD.le
    (by simpa only [neg_mul] using hgap H)
  have hp := cube_mul_exp_neg_le_half_rate c (H : ℝ) hc (Nat.cast_nonneg _)
  calc
    _ ≤ 72 * D * (H : ℝ) ^ 3 * Real.exp (-c * (H : ℝ)) := hs
    _ = (72 * D) * ((H : ℝ) ^ 3 * Real.exp (-c * (H : ℝ))) := by ring
    _ ≤ (72 * D) * ((48 / c ^ 3) * Real.exp (-(c / 2) * (H : ℝ))) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by simp only [neg_mul]; ring

/-- The complementary-turn tail for the exact real primitive-height
cutoff, including the exponential rate and a uniform positive constant. -/
theorem traceBoundary_turn_tail_real :
    ∃ M κ : ℝ, 0 < M ∧ 0 < κ ∧ ∀ H : ℝ, 1 ≤ H →
      (traceBoundaryTurn
        (frontier (Metric.closedBall (0 : TracePlane) 1) \
          realCutoffCorners traceBasis H)).toReal ≤
        M * Real.exp (-(κ * H)) := by
  obtain ⟨M, κ, hM, hκ, htail⟩ := traceBoundary_turn_tail_nat
  refine ⟨M * Real.exp κ, κ, mul_pos hM (Real.exp_pos _), hκ, ?_⟩
  intro H hH
  have hH0 : 0 ≤ H := by linarith
  have hfloor : 1 ≤ ⌊H⌋₊ := (Nat.le_floor_iff hH0).mpr (by simpa using hH)
  rw [realCutoffCorners_eq_natFloor traceBasis H hH0]
  apply (htail ⌊H⌋₊ hfloor).trans
  have he : Real.exp (-(κ * (⌊H⌋₊ : ℝ))) ≤ Real.exp (κ - κ * H) := by
    apply Real.exp_le_exp.mpr
    have hlt := Nat.lt_floor_add_one H
    nlinarith
  calc
    M * Real.exp (-(κ * (⌊H⌋₊ : ℝ))) ≤ M * Real.exp (κ - κ * H) :=
      mul_le_mul_of_nonneg_left he hM.le
    _ = (M * Real.exp κ) * Real.exp (-(κ * H)) := by
      rw [Real.exp_sub, Real.exp_neg]
      ring

/-- Measure-valued form of the full complementary-turn tail. -/
theorem traceBoundary_turn_tail_estimate :
    ∃ M κ : ℝ, 0 < M ∧ 0 < κ ∧ ∀ H : ℝ, 1 ≤ H →
      traceBoundaryTurn
        (frontier (Metric.closedBall (0 : TracePlane) 1) \
          realCutoffCorners traceBasis H) ≤
        ENNReal.ofReal (M * Real.exp (-(κ * H))) := by
  obtain ⟨M, κ, hM, hκ, htail⟩ := traceBoundary_turn_tail_real
  refine ⟨M, κ, hM, hκ, ?_⟩
  intro H hH
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
    (mul_nonneg hM.le (Real.exp_pos _).le)).mpr (htail H hH)

/-- Both quantitative bounds of v1 Theorem 2 for the constructed
trace ball, its normal-turn measure and real cutoffs. -/
theorem traceBoundary_quantitative_turn_estimates :
    ∃ κ K m M : ℝ, 0 < κ ∧ 0 < K ∧ 0 < m ∧ 0 < M ∧
      ∀ H : ℝ, 1 ≤ H →
        traceBoundaryTurn
          (frontier (Metric.closedBall (0 : TracePlane) 1) \
            realCutoffCorners traceBasis H) ≤ ENNReal.ofReal (M * Real.exp (-(κ * H))) ∧
        ∀ x : TracePlane, x ∈ realCutoffCorners traceBasis H →
          ENNReal.ofReal (m * Real.exp (-(K * H))) ≤ traceBoundaryTurn {x} := by
  obtain ⟨M, κ, hM, hκ, htail⟩ := traceBoundary_turn_tail_estimate
  obtain ⟨m, K, hm, hK, hcorner⟩ := traceBoundary_corner_lower_estimate
  exact ⟨κ, K, m, M, hκ, hK, hm, hM, fun H hH => ⟨htail H hH, hcorner H hH⟩⟩

end Markov
