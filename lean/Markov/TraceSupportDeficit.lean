import Markov.TraceCoefficientTail
import Markov.BirthSelectedValues
import Markov.FrickeUpperBranch

/-! The actual inward support deficits of a quadrant Farey pair are
exponentially small in the sum of its two trace-norm lengths. The upper
Fricke branch is discharged by the actual word and its birth height. -/

noncomputable section

namespace Markov

/-- The trace--length relation bounds the reciprocal product of squared
traces by the exponential of minus the sum of the two lengths. -/
theorem inverse_sq_trace_product_le_exp_neg_of_cosh (t b Lu Lv : ℝ)
    (htu : t = 2 * Real.cosh (Lu / 2))
    (hbv : b = 2 * Real.cosh (Lv / 2)) :
    1 / (t ^ 2 * b ^ 2) ≤ Real.exp (-Lu - Lv) := by
  have htu' : Real.exp (Lu / 2) ≤ t := by
    rw [htu, Real.cosh_eq]
    linarith [Real.exp_pos (-(Lu / 2))]
  have hbv' : Real.exp (Lv / 2) ≤ b := by
    rw [hbv, Real.cosh_eq]
    linarith [Real.exp_pos (-(Lv / 2))]
  have ht0 : 0 < t := (Real.exp_pos _).trans_le htu'
  have hb0 : 0 < b := (Real.exp_pos _).trans_le hbv'
  have htu2 : Real.exp Lu ≤ t ^ 2 := by
    calc
      Real.exp Lu = Real.exp (Lu / 2) * Real.exp (Lu / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ t * t := mul_le_mul htu' htu' (Real.exp_pos _).le ht0.le
      _ = _ := by ring
  have hbv2 : Real.exp Lv ≤ b ^ 2 := by
    calc
      Real.exp Lv = Real.exp (Lv / 2) * Real.exp (Lv / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ b * b := mul_le_mul hbv' hbv' (Real.exp_pos _).le hb0.le
      _ = _ := by ring
  have hprod : Real.exp (Lu + Lv) ≤ t ^ 2 * b ^ 2 := by
    rw [Real.exp_add]
    exact mul_le_mul htu2 hbv2 (Real.exp_pos _).le (sq_nonneg _)
  calc
    1 / (t ^ 2 * b ^ 2) ≤ 1 / Real.exp (Lu + Lv) :=
      one_div_le_one_div_of_le (Real.exp_pos _) hprod
    _ = Real.exp (-Lu - Lv) := by
      rw [one_div, ← Real.exp_neg]
      congr 1
      ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Both inward selected-support deficits for an actual seeded word on
the upper Fricke branch, with the explicit reciprocal-trace bound. -/
theorem SeededFarey.support_deficit_bounds (B : Module.Basis (Fin 2) ℝ E)
    {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (hp0 : PositiveFrickePair M0 N0) (hdet0 : intDet u0 v0 ≠ 0)
    (htrace : SeededTraceLengthCompatible B u0 v0 M0 N0)
    (h : SeededFarey u0 v0 M0 N0 u v M N)
    (hupper : M.trace * N.trace ≤ 2 * (M * N).trace) :
    (0 ≤ ‖intVector B u‖ - selectedSupportAt B v u (intVector B u) ∧
      ‖intVector B u‖ - selectedSupportAt B v u (intVector B u) ≤
        96 / ((M.trace : ℝ) ^ 2 * (N.trace : ℝ) ^ 2)) ∧
    (0 ≤ ‖intVector B v‖ - selectedSupportAt B u v (intVector B v) ∧
      ‖intVector B v‖ - selectedSupportAt B u v (intVector B v) ≤
        96 / ((M.trace : ℝ) ^ 2 * (N.trace : ℝ) ^ 2)) := by
  have hp := h.positiveFrickePair hp0
  letI : Fact (3 ≤ M.trace) := ⟨hp.trace_left⟩
  letI : Fact (3 ≤ N.trace) := ⟨hp.trace_right⟩
  have hu := h.reversed_selected_value B hp0 hdet0 htrace
  have hv := h.selected_value B hp0 hdet0 htrace
  have hLu := traceLength_eq_two_log_root M.trace hp.trace_left
    ‖intVector B u‖ (norm_nonneg _) (htrace h).1
  have hLv := traceLength_eq_two_log_root N.trace hp.trace_right
    ‖intVector B v‖ (norm_nonneg _) (htrace h).2
  constructor
  · rw [hLu, hu]
    have hf : N.trace ^ 2 + M.trace ^ 2 + (M * N).trace ^ 2 =
        N.trace * M.trace * (M * N).trace := by nlinarith [hp.fricke]
    have hb := traceCoefficient_logarithmic_deficit_bounds N.trace M.trace
      (M * N).trace hp.trace_left hf (by nlinarith only [hupper])
    simpa only [mul_comm] using hb
  · rw [hLv, hv]
    exact traceCoefficient_logarithmic_deficit_bounds M.trace N.trace
      (M * N).trace hp.trace_right hp.fricke hupper

/-- Exponential form of the two actual inward support deficits. -/
theorem SeededFarey.support_deficit_exp_bounds (B : Module.Basis (Fin 2) ℝ E)
    {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (hp0 : PositiveFrickePair M0 N0) (hdet0 : intDet u0 v0 ≠ 0)
    (htrace : SeededTraceLengthCompatible B u0 v0 M0 N0)
    (h : SeededFarey u0 v0 M0 N0 u v M N)
    (hupper : M.trace * N.trace ≤ 2 * (M * N).trace) :
    (0 ≤ ‖intVector B u‖ - selectedSupportAt B v u (intVector B u) ∧
      ‖intVector B u‖ - selectedSupportAt B v u (intVector B u) ≤
        96 * Real.exp (-‖intVector B u‖ - ‖intVector B v‖)) ∧
    (0 ≤ ‖intVector B v‖ - selectedSupportAt B u v (intVector B v) ∧
      ‖intVector B v‖ - selectedSupportAt B u v (intVector B v) ≤
        96 * Real.exp (-‖intVector B u‖ - ‖intVector B v‖)) := by
  have hb := h.support_deficit_bounds B hp0 hdet0 htrace hupper
  have he := inverse_sq_trace_product_le_exp_neg_of_cosh M.trace N.trace
    ‖intVector B u‖ ‖intVector B v‖ (htrace h).1 (htrace h).2
  have he96 : 96 / ((M.trace : ℝ) ^ 2 * (N.trace : ℝ) ^ 2) ≤
      96 * Real.exp (-‖intVector B u‖ - ‖intVector B v‖) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 96)
  exact ⟨⟨hb.1.1, hb.1.2.trans he96⟩, ⟨hb.2.1, hb.2.2.trans he96⟩⟩

/-- Above birth height one, the actual quadrant word supplies all
upper-branch arithmetic for the inward selected-support estimates. -/
theorem SeededFarey.quadrant_support_deficit_bounds (B : Module.Basis (Fin 2) ℝ E)
    (htrace : QuadrantTraceLengthCompatible B) (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N)
    (hheight : 1 < intHeight (u + v)) :
    (0 ≤ ‖intVector B u‖ - selectedSupportAt B v u (intVector B u) ∧
      ‖intVector B u‖ - selectedSupportAt B v u (intVector B u) ≤
        96 / ((M.trace : ℝ) ^ 2 * (N.trace : ℝ) ^ 2)) ∧
    (0 ≤ ‖intVector B v‖ - selectedSupportAt B u v (intVector B v) ∧
      ‖intVector B v‖ - selectedSupportAt B u v (intVector B v) ≤
        96 / ((M.trace : ℝ) ^ 2 * (N.trace : ℝ) ^ 2)) :=
  h.support_deficit_bounds B (quadrantSeed_positiveFrickePair k)
    (by rw [quadrantSeed_det_eq_one]; norm_num) (htrace k)
    (h.quadrant_upper_branch_of_height k hheight)

/-- Exponential inward support deficits for actual quadrant words. -/
theorem SeededFarey.quadrant_support_deficit_exp_bounds (B : Module.Basis (Fin 2) ℝ E)
    (htrace : QuadrantTraceLengthCompatible B) (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N)
    (hheight : 1 < intHeight (u + v)) :
    (0 ≤ ‖intVector B u‖ - selectedSupportAt B v u (intVector B u) ∧
      ‖intVector B u‖ - selectedSupportAt B v u (intVector B u) ≤
        96 * Real.exp (-‖intVector B u‖ - ‖intVector B v‖)) ∧
    (0 ≤ ‖intVector B v‖ - selectedSupportAt B u v (intVector B v) ∧
      ‖intVector B v‖ - selectedSupportAt B u v (intVector B v) ≤
        96 * Real.exp (-‖intVector B u‖ - ‖intVector B v‖)) :=
  h.support_deficit_exp_bounds B (quadrantSeed_positiveFrickePair k)
    (by rw [quadrantSeed_det_eq_one]; norm_num) (htrace k)
    (h.quadrant_upper_branch_of_height k hheight)

/-- The constructed trace norm has the reciprocal-trace deficit bounds
without any remaining norm/trace compatibility hypothesis. -/
theorem SeededFarey.trace_support_deficit_bounds (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N)
    (hheight : 1 < intHeight (u + v)) :
    (0 ≤ ‖intVector traceBasis u‖ -
        selectedSupportAt traceBasis v u (intVector traceBasis u) ∧
      ‖intVector traceBasis u‖ - selectedSupportAt traceBasis v u (intVector traceBasis u) ≤
        96 / ((M.trace : ℝ) ^ 2 * (N.trace : ℝ) ^ 2)) ∧
    (0 ≤ ‖intVector traceBasis v‖ -
        selectedSupportAt traceBasis u v (intVector traceBasis v) ∧
      ‖intVector traceBasis v‖ - selectedSupportAt traceBasis u v (intVector traceBasis v) ≤
        96 / ((M.trace : ℝ) ^ 2 * (N.trace : ℝ) ^ 2)) :=
  h.quadrant_support_deficit_bounds traceBasis tracePlane_quadrantTraceLengthCompatible k hheight

/-- The constructed trace norm has the exponential inward deficit bounds
at every actual quadrant pair whose birth height exceeds one. -/
theorem SeededFarey.trace_support_deficit_exp_bounds (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N)
    (hheight : 1 < intHeight (u + v)) :
    (0 ≤ ‖intVector traceBasis u‖ -
        selectedSupportAt traceBasis v u (intVector traceBasis u) ∧
      ‖intVector traceBasis u‖ - selectedSupportAt traceBasis v u (intVector traceBasis u) ≤
        96 * Real.exp (-‖intVector traceBasis u‖ - ‖intVector traceBasis v‖)) ∧
    (0 ≤ ‖intVector traceBasis v‖ -
        selectedSupportAt traceBasis u v (intVector traceBasis v) ∧
      ‖intVector traceBasis v‖ - selectedSupportAt traceBasis u v (intVector traceBasis v) ≤
        96 * Real.exp (-‖intVector traceBasis u‖ - ‖intVector traceBasis v‖)) :=
  h.quadrant_support_deficit_exp_bounds traceBasis tracePlane_quadrantTraceLengthCompatible k hheight

end Markov
