import Markov.CutoffParameterBounds

/-! A uniform logarithmic choice of the intermediate cutoff.  The constant
only depends on the diameter and corner constants; it is independent of
the angular error and of both cutoff parameters. -/

namespace Markov

/-- The exponential bound used for the logarithmic intermediate cutoff. -/
theorem logarithmic_cutoff_decay
    (C c D T : ℝ) (hC : 0 < C) (hT : 1 ≤ T)
    (hD : 3 + C / Real.log 2 ≤ c * D) :
    C * Real.exp (-c * (D * Real.log (2 * T))) < 1 / T ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlog : Real.log (2 * T) = Real.log 2 + Real.log T :=
    Real.log_mul (by norm_num) hT0.ne'
  have hloglow : Real.log 2 ≤ Real.log (2 * T) := by linarith
  have hlog0 : 0 ≤ Real.log (2 * T) := by linarith
  have hmain := mul_le_mul_of_nonneg_right hD hlog0
  have hpart := mul_le_mul_of_nonneg_left hloglow
    (show 0 ≤ C / Real.log 2 by positivity)
  rw [div_mul_cancel₀ _ hl2.ne'] at hpart
  have hrate : C + 3 * Real.log (2 * T) ≤ c * D * Real.log (2 * T) := by
    nlinarith
  have hlogC := Real.log_le_sub_one_of_pos hC
  have hexponent : Real.log C - c * (D * Real.log (2 * T)) <
      -(2 * Real.log T) := by
    nlinarith
  calc
    C * Real.exp (-c * (D * Real.log (2 * T))) =
        Real.exp (Real.log C - c * (D * Real.log (2 * T))) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hC]
      simp only [neg_mul]
    _ < Real.exp (-(2 * Real.log T)) := Real.exp_lt_exp.mpr hexponent
    _ = 1 / T ^ 2 := by
      rw [Real.exp_neg, show (2 : ℝ) * Real.log T = (2 : ℕ) * Real.log T by norm_num,
        Real.exp_nat_mul, Real.exp_log hT0]
      simp only [one_div]

/-- There is a positive logarithmic cutoff coefficient, uniform in the
angular error and in the two cutoff heights.  The basic assumption at
height `H` makes the diameter plus twice the angular error strictly
smaller than `T⁻²` at the intermediate height `D * log (2 * T)`. -/
theorem exists_logarithmic_cutoff_constant
    (M m κ Kcorner : ℝ) (hM : 0 < M) (hm : 0 < m)
    (hκ : 0 < κ) (hKcorner : 0 < Kcorner) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (ε K T H η : ℝ), 0 < ε → 1 ≤ T → T ≤ K → 0 ≤ η →
        (2 + ε) * η ≤ m * Real.exp (-Kcorner * H) →
        D * Real.log (2 * K) ≤ H →
        1 ≤ D * Real.log (2 * T) ∧
        D * Real.log (2 * T) ≤ H ∧
        M * Real.exp (-κ * (D * Real.log (2 * T))) + 2 * η < 1 / T ^ 2 := by
  let C := M + m
  let c := min κ Kcorner
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : 0 < c := lt_min hκ hKcorner
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D := 1 / Real.log 2 + (3 + C / Real.log 2) / c
  have hD : 0 < D := by dsimp [D]; positivity
  have hDone : 1 ≤ D * Real.log 2 := by
    have heq : (1 / Real.log 2) * Real.log 2 = 1 :=
      div_mul_cancel₀ 1 hl2.ne'
    have hpos : 0 ≤ ((3 + C / Real.log 2) / c) * Real.log 2 := by positivity
    dsimp [D]
    nlinarith
  have hDdecay : 3 + C / Real.log 2 ≤ c * D := by
    have heq : c * D = c / Real.log 2 + (3 + C / Real.log 2) := by
      dsimp [D]
      field_simp
    rw [heq]
    have : 0 ≤ c / Real.log 2 := by positivity
    linarith
  refine ⟨D, hD, ?_⟩
  intro ε K T H η hε hT hTK hη0 hη hH
  have hT0 : 0 < T := by linarith
  have hloglow : Real.log 2 ≤ Real.log (2 * T) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hh1 : 1 ≤ D * Real.log (2 * T) :=
    hDone.trans (mul_le_mul_of_nonneg_left hloglow hD.le)
  have hlogTK : Real.log (2 * T) ≤ Real.log (2 * K) :=
    Real.log_le_log (by positivity) (by linarith)
  have hhH : D * Real.log (2 * T) ≤ H :=
    (mul_le_mul_of_nonneg_left hlogTK hD.le).trans hH
  have hH0 : 0 ≤ H := by linarith
  have heta := cutoff_eta_le_common_rate_of_basic_assumption
    m ε κ Kcorner H η hm hε hH0 hη
  have hcorner : 2 * η ≤ m * Real.exp (-c * (D * Real.log (2 * T))) := by
    have hexp : Real.exp (-c * H) ≤
        Real.exp (-c * (D * Real.log (2 * T))) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hexp hm.le
    change η ≤ m / 2 * Real.exp (-c * H) at heta
    nlinarith
  have hdiam : M * Real.exp (-κ * (D * Real.log (2 * T))) ≤
      M * Real.exp (-c * (D * Real.log (2 * T))) := by
    apply mul_le_mul_of_nonneg_left _ hM.le
    apply Real.exp_le_exp.mpr
    have hcle : c ≤ κ := min_le_left κ Kcorner
    have hh0 : 0 ≤ D * Real.log (2 * T) := by linarith
    nlinarith
  refine ⟨hh1, hhH, ?_⟩
  have hwidth : M * Real.exp (-κ * (D * Real.log (2 * T))) + 2 * η ≤
      C * Real.exp (-c * (D * Real.log (2 * T))) := by
    dsimp [C]
    nlinarith
  exact hwidth.trans_lt (logarithmic_cutoff_decay C c D T hC hT hDdecay)

end Markov
