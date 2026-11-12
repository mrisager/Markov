import Markov.Covectors

/-! The exponential size estimates in Lemma 5, derived from the actual
trace-field elements. No exponential size bound is assumed in this module. -/

noncomputable section
attribute [-instance] DivisionRing.toRatAlgebra
local instance : Algebra ℚ ℝ := DivisionRing.toRatAlgebra

namespace Markov

theorem positiveTraceRoot_add_inv (t : ℤ) (ht : 3 ≤ t) :
    positiveTraceRoot t + (positiveTraceRoot t)⁻¹ = (t : ℝ) := by
  have hr : 0 < positiveTraceRoot t := by linarith [positiveTraceRoot_gt_one t ht]
  have hi : (1 : ℝ) / positiveTraceRoot t = (t : ℝ) - positiveTraceRoot t := by
    apply (div_eq_iff hr.ne').mpr
    nlinarith [positiveTraceRoot_equation t ht]
  rw [← one_div, hi]
  ring

theorem positiveTraceRoot_lt_trace (t : ℤ) (ht : 3 ≤ t) : positiveTraceRoot t < (t : ℝ) := by
  have hr : 0 < positiveTraceRoot t := by linarith [positiveTraceRoot_gt_one t ht]
  linarith [positiveTraceRoot_add_inv t ht, inv_pos.mpr hr]

theorem positiveTraceRoot_abs_log_le (t : ℤ) (ht : 3 ≤ t) :
    |Real.log (positiveTraceRoot t)| ≤ Real.log (t : ℝ) := by
  rw [abs_of_nonneg (Real.log_nonneg (positiveTraceRoot_gt_one t ht).le)]
  exact Real.log_le_log (by linarith [positiveTraceRoot_gt_one t ht])
    (positiveTraceRoot_lt_trace t ht).le

theorem positive_pair_reciprocal_bounds (a a' B : ℝ) (ha : 0 < a) (ha' : 0 < a')
    (hB : 0 < B) (hsum : a + a' = B) (hprod : 1 < a * a') :
    1 / B < a ∧ a < B ∧ 1 / B < a' ∧ a' < B := by
  have hu : a < B := by linarith
  have hu' : a' < B := by linarith
  refine ⟨?_, hu, ?_, hu'⟩
  · apply (div_lt_iff₀ hB).mpr
    nlinarith [mul_lt_mul_of_pos_right hu' ha]
  · apply (div_lt_iff₀ hB).mpr
    nlinarith [mul_lt_mul_of_pos_right hu ha']

theorem abs_log_le_of_reciprocal_bounds (a B : ℝ) (ha : 0 < a) (hB : 0 < B)
    (hl : 1 / B ≤ a) (hu : a ≤ B) : |Real.log a| ≤ Real.log B := by
  rw [abs_le]
  refine ⟨?_, Real.log_le_log ha hu⟩
  have h := Real.log_le_log (one_div_pos.mpr hB) hl
  simpa only [one_div, Real.log_inv] using h

/-- Equation (58) in the paper, for both actual real conjugates. -/
theorem traceCoefficient_real_bounds (t b c : ℤ) [ht : Fact (3 ≤ t)] (hb : 0 < b)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) :
    let a := traceRealEmbedding t (traceCoefficient t b c)
    let a' := traceRealEmbedding t (star (traceCoefficient t b c))
    1 / (b : ℝ) < a ∧ a < (b : ℝ) ∧ 1 / (b : ℝ) < a' ∧ a' < (b : ℝ) := by
  have hpos := traceCoefficient_real_pos t b c hb hf
  have hs := congrArg (traceRealEmbedding t) (traceCoefficient_add_star t b c ht.out)
  simp only [map_add, map_intCast] at hs
  have hn : (1 : ℝ) < (Algebra.norm ℚ (traceCoefficient t b c) : ℝ) := by
    exact_mod_cast traceCoefficient_field_norm_gt_one t b c ht.out hf
  rw [traceField_real_norm_eq] at hn
  exact positive_pair_reciprocal_bounds _ _ _ hpos.1 hpos.2 (by exact_mod_cast hb) hs hn

theorem traceCoefficient_abs_log_le (t b c : ℤ) [Fact (3 ≤ t)] (hb : 0 < b)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) :
    |Real.log (traceRealEmbedding t (traceCoefficient t b c))| ≤ Real.log (b : ℝ) ∧
      |Real.log (traceRealEmbedding t (star (traceCoefficient t b c)))| ≤ Real.log (b : ℝ) := by
  have hpos := traceCoefficient_real_pos t b c hb hf
  obtain ⟨hl, hu, hl', hu'⟩ := traceCoefficient_real_bounds t b c hb hf
  exact ⟨abs_log_le_of_reciprocal_bounds _ _ hpos.1 (by exact_mod_cast hb) hl.le hu.le,
    abs_log_le_of_reciprocal_bounds _ _ hpos.2 (by exact_mod_cast hb) hl'.le hu'.le⟩

theorem zpow_le_exp_of_abs_log_le (a L : ℝ) (m : ℤ) (ha : 0 < a)
    (hlog : |Real.log a| ≤ L) : a ^ m ≤ Real.exp (|(m : ℝ)| * L) := by
  calc
    a ^ m = Real.exp ((m : ℝ) * Real.log a) := by
      rw [← Real.log_zpow, Real.exp_log (zpow_pos ha m)]
    _ ≤ Real.exp (|(m : ℝ)| * L) := by
      apply Real.exp_le_exp.mpr
      calc
        (m : ℝ) * Real.log a ≤ |(m : ℝ) * Real.log a| := le_abs_self _
        _ = |(m : ℝ)| * |Real.log a| := abs_mul _ _
        _ ≤ |(m : ℝ)| * L := mul_le_mul_of_nonneg_left hlog (abs_nonneg _)

/-- The clearing-factor bound in equation (61), before inserting height estimates. -/
theorem traceClearingFactor_exp_bound (t n : ℤ) (ht : 3 ≤ t) :
    (traceClearingFactor t n : ℝ) ≤ Real.exp (2 * |(n : ℝ)| * Real.log (t : ℝ)) := by
  have ht' : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hD0 : (0 : ℝ) < traceClearingFactor t n := by
    exact_mod_cast traceClearingFactor_pos t n ht
  apply (Real.log_le_iff_le_exp hD0).mp
  have hΔ : (0 : ℝ) < (t : ℝ) ^ 2 - 4 := by nlinarith
  have hΔlog : Real.log ((t : ℝ) ^ 2 - 4) ≤ 2 * Real.log (t : ℝ) := by
    calc
      _ ≤ Real.log ((t : ℝ) ^ 2) := Real.log_le_log hΔ (by linarith)
      _ = 2 * Real.log (t : ℝ) := by rw [Real.log_pow]; norm_num
  cases n with
  | ofNat k =>
    simp only [traceClearingFactor, Int.cast_pow, Real.log_pow]
    change ((2 * k : ℕ) : ℝ) * Real.log (t : ℝ) ≤ 2 * |(k : ℝ)| * Real.log (t : ℝ)
    rw [abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) by positivity)]
    push_cast
    nlinarith
  | negSucc k =>
    simp only [traceClearingFactor, Int.cast_pow, Int.cast_sub, Int.cast_ofNat,
      Real.log_pow, Int.cast_negSucc, abs_neg]
    have hm := mul_le_mul_of_nonneg_left hΔlog (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)
    push_cast
    rw [abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)]
    nlinarith

/-- The conjugate bound in equation (61), before inserting height estimates. -/
theorem traceBeta_conjugate_exp_bound (t b c : ℤ) [ht : Fact (3 ≤ t)] (hb : 0 < b)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) (m n : ℤ) :
    traceRealEmbedding t (star (traceRoot t ^ m * traceCoefficient t b c ^ (-n))) ≤
      Real.exp (|(m : ℝ)| * Real.log (t : ℝ) + |(n : ℝ)| * Real.log (b : ℝ)) := by
  have hpos := traceCoefficient_real_pos t b c hb hf
  have hlogs := traceCoefficient_abs_log_le t b c hb hf
  have hr0 : 0 < positiveTraceRoot t := by linarith [positiveTraceRoot_gt_one t ht.out]
  have hrlog : |Real.log (positiveTraceRoot t)⁻¹| ≤ Real.log (t : ℝ) := by
    simpa only [Real.log_inv, abs_neg] using positiveTraceRoot_abs_log_le t ht.out
  rw [star_mul, star_zpow₀, star_zpow₀, map_mul, map_zpow₀, map_zpow₀,
    traceRoot_star_eq_inv, map_inv₀, traceRealEmbedding_root]
  calc
    _ ≤ Real.exp (|((-n : ℤ) : ℝ)| * Real.log (b : ℝ)) *
        Real.exp (|(m : ℝ)| * Real.log (t : ℝ)) :=
      mul_le_mul (zpow_le_exp_of_abs_log_le _ _ (-n) hpos.2 hlogs.2)
        (zpow_le_exp_of_abs_log_le _ _ m (inv_pos.mpr hr0) hrlog)
        (zpow_pos (inv_pos.mpr hr0) m).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; simp only [Int.cast_neg, abs_neg]; congr 1; ring

end Markov
