import T1VKWeight

/-! The Vinogradov–Korobov weight diverges, but is sublogarithmic. -/
noncomputable section
open Filter Asymptotics
namespace Markov

theorem t1_vkWeight_tendsto : Tendsto t1_vkWeight atTop atTop := by
  have hp : Tendsto (fun R => (Real.log R)^((2 : ℝ)/5)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<(2 : ℝ)/5)).comp Real.tendsto_log_atTop
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [hp.eventually_ge_atTop b,Real.tendsto_log_atTop.eventually_gt_atTop 1]
    with R hb hR
  have hR0 : 0 < Real.log R := by linarith
  have hll := Real.log_pos hR
  have hd : (Real.log (Real.log R))^((1 : ℝ)/5) ≤ (Real.log R)^((1 : ℝ)/5) :=
    Real.rpow_le_rpow hll.le (by linarith [Real.log_le_sub_one_of_pos hR0]) (by norm_num)
  refine hb.trans ?_
  have he : (2 : ℝ)/5 = 3/5-1/5 := by norm_num
  rw [he,Real.rpow_sub hR0,t1_vkWeight]
  exact (div_le_div_iff₀ (Real.rpow_pos_of_pos hR0 _) (Real.rpow_pos_of_pos hll _)).2
    (mul_le_mul_of_nonneg_left hd (by positivity))

theorem t1_vkWeight_isLittleO_log : t1_vkWeight =o[atTop] Real.log := by
  have hsmall : (fun R => (Real.log R)^((3 : ℝ)/5)) =o[atTop] Real.log := by
    apply isLittleO_of_tendsto' ?_
    · have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<2/5)).comp
        Real.tendsto_log_atTop
      apply h.congr'
      filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with R hR
      change (Real.log R)^(-((2 : ℝ)/5)) = (Real.log R)^((3 : ℝ)/5)/Real.log R
      rw [show -((2 : ℝ)/5) = 3/5-1 by norm_num,Real.rpow_sub_one hR.ne']
    · filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with R hR
      exact fun h => (hR.ne' h).elim
  refine (IsBigO.of_bound (c := 1) ?_).trans_isLittleO hsmall
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1] with R hR hll
  have hR0 : 0 < Real.log R := by linarith
  have hp : 0 ≤ (Real.log R)^((3 : ℝ)/5) := Real.rpow_nonneg hR0.le _
  change 1 ≤ Real.log (Real.log R) at hll
  have hd := Real.one_le_rpow hll (by norm_num : (0 : ℝ)≤(1 : ℝ)/5)
  have hd0 : 0 < (Real.log (Real.log R))^((1 : ℝ)/5) := by linarith
  have hv : 0 ≤ t1_vkWeight R := div_nonneg hp hd0.le
  simp only [Real.norm_eq_abs,abs_of_nonneg hv,abs_of_nonneg hp,one_mul]
  exact (div_le_iff₀ hd0).2 (le_mul_of_one_le_right hp hd)

theorem t1_vkWeight_half_log (R : ℝ) (hR : Real.exp 2 < R) :
    t1_vkWeight (R^((1 : ℝ)/2)) ≥ t1_vkWeight R / 2 := by
  have hR0 := (Real.exp_pos _).trans hR
  have hl : 2 < Real.log R := by
    rw [← Real.log_exp (2 : ℝ)]
    exact Real.log_lt_log (Real.exp_pos _) hR
  have hl0 : 0 < Real.log R := by linarith
  have hl' : 1 < ((1 : ℝ)/2)*Real.log R := by linarith
  have hll := Real.log_pos (show 1 < Real.log R by linarith)
  have hll' := Real.log_pos hl'
  have hmono := Real.log_le_log (by linarith : 0 < ((1 : ℝ)/2)*Real.log R)
    (by linarith : ((1 : ℝ)/2)*Real.log R ≤ Real.log R)
  have hd := Real.rpow_le_rpow hll'.le hmono
    (show 0 ≤ (1 : ℝ)/5 by norm_num)
  have hn := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1 : ℝ)/2 ≤ 1) (by norm_num : (3 : ℝ)/5 ≤ 1)
  rw [Real.rpow_one] at hn
  change t1_vkWeight R / 2 ≤ t1_vkWeight (R^((1 : ℝ)/2))
  unfold t1_vkWeight
  rw [Real.log_rpow hR0,Real.mul_rpow (by norm_num : (0 : ℝ)≤1/2) hl0.le]
  have hp : 0 ≤ (Real.log R)^((3 : ℝ)/5) := Real.rpow_nonneg hl0.le _
  calc
    _ = (((1 : ℝ)/2)*(Real.log R)^((3 : ℝ)/5))/(Real.log (Real.log R))^((1 : ℝ)/5) := by ring
    _ ≤ (((1 : ℝ)/2)^((3 : ℝ)/5)*(Real.log R)^((3 : ℝ)/5))/
        (Real.log (Real.log R))^((1 : ℝ)/5) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hn hp) (by positivity)
    _ ≤ _ := (div_le_div_iff₀ (Real.rpow_pos_of_pos hll _) (Real.rpow_pos_of_pos hll' _)).2
      (mul_le_mul_of_nonneg_left hd (by positivity))

end Markov
