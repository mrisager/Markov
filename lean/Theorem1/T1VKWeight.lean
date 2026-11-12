import T1PrimitiveErrorScales

/-! Properties of the real Vinogradov–Korobov weight. These are
properties of the cutoff parameter, independent of Möbius cancellation. -/
noncomputable section
open Filter Asymptotics
namespace Markov

def t1_vkWeight (R : ℝ) : ℝ :=
  (Real.log R)^((3 : ℝ)/5)/(Real.log (Real.log R))^((1 : ℝ)/5)

theorem t1_vkWeight_pos (R : ℝ) (hR : Real.exp 1 < R) :
    0 < t1_vkWeight R := by
  have hlog : 1 < Real.log R := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_lt_log (Real.exp_pos _) hR
  exact div_pos (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_pos_of_pos (Real.log_pos hlog) _)

theorem t1_vkWeight_as_rpow (R : ℝ) (hR : Real.exp 1 < R) :
    t1_vkWeight R = ((Real.log R)^3/Real.log (Real.log R))^((1 : ℝ)/5) := by
  have hlog : 1 < Real.log R := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_lt_log (Real.exp_pos _) hR
  unfold t1_vkWeight
  rw [Real.div_rpow (by positivity) (Real.log_pos hlog).le,
    ← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ Real.log R)]
  congr 2
  norm_num

theorem t1_vkWeight_monotone :
    MonotoneOn t1_vkWeight (Set.Ici (Real.exp (Real.exp 1))) := by
  intro R hR S hS hRS
  have h1 : 1 < Real.exp 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hR' : Real.exp 1 < R :=
    (Real.exp_lt_exp.mpr h1).trans_le hR
  have hu : Real.exp 1 ≤ Real.log R := by
    rw [← Real.log_exp (Real.exp 1)]
    exact Real.log_le_log (Real.exp_pos _) hR
  have huv := Real.log_le_log ((Real.exp_pos _).trans hR') hRS
  let u := Real.log R
  let v := Real.log S
  have hu0 : 0 < u := (Real.exp_pos _).trans_le hu
  have hv0 : 0 < v := hu0.trans_le huv
  have hlogu : 1 ≤ Real.log u := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_le_log (Real.exp_pos _) hu
  have hlogv : 0 < Real.log v :=
    (by linarith : 0 < Real.log u).trans_le (Real.log_le_log hu0 huv)
  have hratio : 1 ≤ v/u := (le_div_iff₀ hu0).2 (by simpa only [one_mul] using huv)
  have hh := Real.log_le_sub_one_of_pos (div_pos hv0 hu0)
  rw [Real.log_div hv0.ne' hu0.ne'] at hh
  have hlogle : Real.log v ≤ (v/u)*Real.log u := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hratio) (sub_nonneg.mpr hlogu)]
  have hprod : u^3*Real.log v ≤ v^3*Real.log u := calc
    _ ≤ u^3*((v/u)*Real.log u) := mul_le_mul_of_nonneg_left hlogle (by positivity)
    _ = (u^2*v)*Real.log u := by field_simp [hu0.ne']
    _ ≤ v^3*Real.log u := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      rw [pow_succ v 2]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu0.le huv 2) hv0.le
  have hdiv := (div_le_div_iff₀ (by linarith : 0 < Real.log u) hlogv).2 hprod
  rw [t1_vkWeight_as_rpow R hR',t1_vkWeight_as_rpow S (hR'.trans_le hRS)]
  exact Real.rpow_le_rpow (div_nonneg (by positivity) (by linarith)) hdiv (by norm_num)

end Markov
