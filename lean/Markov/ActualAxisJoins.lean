import Markov.FrontierAxes
import Markov.SeedEnvelope
import Markov.TraceLengthBounds

/-! The corner inequalities for the two actual finite profiles meeting at
the coordinate axes. Their endpoint values are calculated from the concrete
matrix rays, and the opposite-ray Fricke inequality supplies each join. -/

namespace Markov

private theorem axis_trace_three_length :
    2 * Real.arcosh ((3 : ℝ) / 2) =
      2 * Real.log (positiveTraceRoot 3) := by
  apply traceLength_eq_two_log_root (3 : ℤ) (by norm_num)
  · exact mul_nonneg (by norm_num) (Real.arcosh_nonneg (by norm_num))
  · have hh : (2 * Real.arcosh ((3 : ℝ) / 2)) / 2 =
        Real.arcosh ((3 : ℝ) / 2) := by ring
    rw [hh, Real.cosh_arcosh (by norm_num)]
    norm_num

/-- The two actual frontier profiles satisfy the finite join at the first
coordinate axis. -/
theorem actual_axis_join_zero (n : ℕ) :
    -(seedFrontierOffsets modularGeneratorB modularGeneratorA.adjugate n 0 +
        seedFrontierSlopes modularGeneratorB modularGeneratorA.adjugate n 0) ≤
      seedFrontierOffsets modularGeneratorA modularGeneratorB n (2 ^ n - 1) := by
  change -(seedEdgeOffset _ _ _ + seedEdgeSlope _ _ _) ≤ seedEdgeOffset _ _ _
  rw [seedEdgeOffset_add_slope_first_axis, seedEdgeOffset_last_axis]
  have hp : PositiveFrickePair modularGeneratorB modularGeneratorA.adjugate := by
    simpa only [quadrantSeedMatrices] using quadrantSeed_positiveFrickePair 1
  have hh := positiveFrickePair_axis_corner_equal modularGeneratorB
    modularGeneratorA.adjugate hp n
  have hadj : modularGeneratorA.adjugate.adjugate = modularGeneratorA := by
    simp only [Matrix.adjugate_adjugate', Fintype.card_fin, Nat.sub_self,
      pow_zero, one_smul]
  rw [hadj, Matrix.trace_mul_comm (modularGeneratorB ^ n) modularGeneratorA] at hh
  have hB : modularGeneratorB.trace = 3 := by
    norm_num [modularGeneratorB, Matrix.trace, Matrix.diag_apply]
  rw [hB] at hh ⊢
  norm_num only [Int.cast_ofNat] at ⊢
  rw [axis_trace_three_length]
  linarith

/-- The two actual frontier profiles satisfy the finite join at the second
coordinate axis. -/
theorem actual_axis_join_one (n : ℕ) :
    -(seedFrontierOffsets modularGeneratorA modularGeneratorB n 0 +
        seedFrontierSlopes modularGeneratorA modularGeneratorB n 0) ≤
      seedFrontierOffsets modularGeneratorB modularGeneratorA.adjugate n (2 ^ n - 1) := by
  change -(seedEdgeOffset _ _ _ + seedEdgeSlope _ _ _) ≤ seedEdgeOffset _ _ _
  rw [seedEdgeOffset_add_slope_first_axis, seedEdgeOffset_last_axis]
  have hh := positiveFrickePair_axis_corner_equal modularGeneratorA
    modularGeneratorB seed_positiveFrickePair n
  have hA : modularGeneratorA.trace = 3 := by
    norm_num [modularGeneratorA, Matrix.trace, Matrix.diag_apply]
  rw [matrix_two_trace_adjugate] 
  rw [Matrix.trace_mul_comm modularGeneratorB (modularGeneratorA.adjugate ^ n),
    matrix_two_trace_adjugate_power_mul]
  rw [hA] at hh ⊢
  norm_num only [Int.cast_ofNat] at ⊢
  rw [axis_trace_three_length]
  linarith

end Markov
