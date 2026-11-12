import Markov.TraceChordAngleEnvelope
import Markov.TraceRationalArcDecay
import Markov.TracePositiveConeArc
import Markov.SlopeArcPositiveCone
import Markov.CutoffGapHeightBounds
import Markov.AngleEnvelopeCutoff
import Markov.TailPolynomialAbsorption

/-! Exponential decay of the actual canonical cutoff support-angle
envelope. Its decay is derived from actual trace/support data and full
boundary turn, rather than retained as a geometric hypothesis. -/

noncomputable section
open Set
namespace Markov

/-- An actual canonical cutoff gap is contained in the rational open arc
of an actual quadrant-zero matrix word with the same endpoint directions. -/
theorem traceCutoffArc_exists_quadrant_zero_word (n : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes n u v) :
    ∃ M N : IntMatrixTwo,
      SeededFarey (quadrantSeedDirections 0).1 (quadrantSeedDirections 0).2
        (quadrantSeedMatrices 0).1 (quadrantSeedMatrices 0).2 u v M N ∧
      traceCutoffArc u v ⊆ traceBoundaryOpenArc
        (traceRationalParameter 0 u) (traceRationalParameter 0 v) := by
  have hu := (mem_cutoffSlopesUpTo n u).mp h.1
  have hv := (mem_cutoffSlopesUpTo n v).mp h.2.1
  obtain ⟨M, N, hword⟩ := exists_quadrantSeededFarey_of_coordinates 0 u v
    hu.1.le hu.2.1 hv.1.le hv.2.1
    (consecutiveCutoffSlopes_det_and_denominator_sum n u v h).1
  refine ⟨M, N, hword, ?_⟩
  intro x hx
  obtain ⟨α, β, hα, hβ, he⟩ :=
    consecutiveCutoffSlopes_mem_arc_exists_pos_intVector_combination traceBasis n u v h x hx
  rw [← he]
  exact hword.normalize_positiveCombination_mem_traceBoundaryOpenArc α β hα hβ

/-- The previously explicit actual-envelope width input has a uniform
positive exponential bound at every positive canonical integer cutoff. -/
theorem trace_cutoff_supportAngle_width_decay :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ u v : ℤ × ℤ, ConsecutiveCutoffSlopes n u v →
        supportAngleUpper traceBasis (traceCutoffArc u v) -
          supportAngleLower traceBasis (traceCutoffArc u v) ≤
          M * Real.exp (-c * (n : ℝ)) := by
  obtain ⟨C, c, hC, hc, hdecay⟩ := trace_rational_arc_turn_height_decay
  refine ⟨(2 * C) * (48 / c ^ 3), c / 2, by positivity, by positivity, ?_⟩
  intro n hn u v h
  obtain ⟨M, N, hword, hsub⟩ := traceCutoffArc_exists_quadrant_zero_word n u v h
  have huI := hword.traceRationalQuarterParameter_left_mem_Icc
  have hvI := hword.traceRationalQuarterParameter_right_mem_Icc
  have hwidth := supportAngleWidth_le_traceBoundaryTurn_chord_openArc 0
    (traceRationalQuarterParameter 0 u) (traceRationalQuarterParameter 0 v)
    huI.1 hword.traceRationalQuarterParameter_lt hvI.2
    (traceCutoffArc u v) (traceCutoffArc_nonempty n u v h) hsub
  obtain ⟨_, _, _, _, _, _, hsumH, hsum2H, hheight, _⟩ :=
    signedConsecutiveCutoffSlopes_height_bounds 0 n u v h
  simp only [inverseSignedSectorCoordinates_height] at hsumH hsum2H
  have hheight' : 1 < intHeight (u + v) := by
    simpa only [inverseSignedSectorCoordinates_height_add] using hheight
  have harc := hdecay 0 u v M N hword hheight'
  apply (hwidth.trans harc).trans
  have he : Real.exp (-(c * (intHeight u + intHeight v))) ≤
      Real.exp (-c * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hfirst : C * (intHeight u + intHeight v) *
      Real.exp (-(c * (intHeight u + intHeight v))) ≤
        (2 * C) * (n : ℝ) * Real.exp (-c * (n : ℝ)) := by
    convert mul_le_mul (mul_le_mul_of_nonneg_left hsum2H hC.le) he
      (Real.exp_pos _).le (by positivity : 0 ≤ C * (2 * (n : ℝ))) using 1
    ring
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcube : (n : ℝ) ≤ (n : ℝ) ^ 3 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hp := cube_mul_exp_neg_le_half_rate c (n : ℝ) hc (Nat.cast_nonneg _)
  calc
    _ ≤ (2 * C) * (n : ℝ) * Real.exp (-c * (n : ℝ)) := hfirst
    _ ≤ (2 * C) * ((n : ℝ) ^ 3 * Real.exp (-c * (n : ℝ))) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcube (by positivity)) (Real.exp_pos _).le
    _ ≤ (2 * C) * ((48 / c ^ 3) * Real.exp (-(c / 2) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- Actual Euclidean normal diameter now has exponential cutoff decay;
the decay is a conclusion, not an intermediate hypothesis. -/
theorem trace_cutoff_normal_diam_decay :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ u v : ℤ × ℤ, ConsecutiveCutoffSlopes n u v →
        Metric.diam (normalsOn traceBasis (traceCutoffArc u v)) ≤
          M * Real.exp (-c * (n : ℝ)) := by
  obtain ⟨M, c, hM, hc, hwidth⟩ := trace_cutoff_supportAngle_width_decay
  exact ⟨M, c, hM, hc, fun n hn u v h =>
    trace_cutoff_normal_diam_le_of_supportAngle_width n u v h M c (hwidth n hn u v h)⟩

end Markov
