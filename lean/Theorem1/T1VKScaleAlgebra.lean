import T1VKWeightGrowth

/-! The exact unconditional scale is R times the inverse square root of
the Vinogradov–Korobov weight. The exponentially small tail is negligible. -/
noncomputable section
open Filter Asymptotics
namespace Markov

theorem t1_primitiveUnconditionalScale_vkWeight (R : ℝ) (hR : Real.exp 1 < R) :
    primitiveUnconditionalScale R = R/(t1_vkWeight R)^((1 : ℝ)/2) := by
  have hl : 1 < Real.log R := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_lt_log (Real.exp_pos _) hR
  have hl0 : 0 < Real.log R := by linarith
  have hll := Real.log_pos hl
  change R*(Real.log (Real.log R))^((1 : ℝ)/10)/(Real.log R)^((3 : ℝ)/10) =
    R/(t1_vkWeight R)^((1 : ℝ)/2)
  rw [t1_vkWeight,Real.div_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hl0.le,← Real.rpow_mul hll.le,
    show ((3 : ℝ)/5)*(1/2) = 3/10 by norm_num,
    show ((1 : ℝ)/5)*(1/2) = 1/10 by norm_num]
  rw [div_div_eq_mul_div]

theorem t1_vk_tail_isLittleO (b : ℝ) (hb : 0 < b) :
    (fun R => R*Real.exp (-b*t1_vkWeight R)) =o[atTop] primitiveUnconditionalScale := by
  apply isLittleO_of_tendsto' ?_
  · have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((1 : ℝ)/2) b hb).comp
      t1_vkWeight_tendsto
    apply h.congr'
    filter_upwards [eventually_gt_atTop (Real.exp 1)] with R hR
    have hR0 := (Real.exp_pos _).trans hR
    have hW := t1_vkWeight_pos R hR
    change (t1_vkWeight R)^((1 : ℝ)/2)*Real.exp (-b*t1_vkWeight R) =
      R*Real.exp (-b*t1_vkWeight R)/primitiveUnconditionalScale R
    rw [t1_primitiveUnconditionalScale_vkWeight R hR,div_div_eq_mul_div]
    field_simp
  · filter_upwards [eventually_gt_atTop (Real.exp 1)] with R hR
    exact fun he => ((t1_primitiveUnconditionalScale_pos R hR).ne' he).elim

end Markov
