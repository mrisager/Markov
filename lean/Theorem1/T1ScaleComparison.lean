import T1PrimitiveErrorScales

/-! Uniform comparison of the exact two primitive scales when the
argument is enlarged by at most a factor of four. -/
noncomputable section
namespace Markov

theorem t1_primitiveConditionalScale_compare (R L : ℝ) (hR : 1 < R)
    (hRL : R ≤ L) (hL : L ≤ 4*R) :
    primitiveConditionalScale L ≤ 4*primitiveConditionalScale R := by
  have hR0 : 0 < R := by linarith
  have hlogR := Real.log_pos hR
  have hlog := Real.log_le_log hR0 hRL
  have hlogL : 0 < Real.log L := hlogR.trans_le hlog
  have hdR := Real.rpow_pos_of_pos hlogR ((1 : ℝ)/2)
  have hdL := Real.rpow_pos_of_pos hlogL ((1 : ℝ)/2)
  have hd := Real.rpow_le_rpow hlogR.le hlog (by norm_num : 0 ≤ (1 : ℝ)/2)
  change L/(Real.log L)^((1 : ℝ)/2) ≤ 4*(R/(Real.log R)^((1 : ℝ)/2))
  calc
    _ ≤ (4*R)/(Real.log L)^((1 : ℝ)/2) := div_le_div_of_nonneg_right hL hdL.le
    _ ≤ (4*R)/(Real.log R)^((1 : ℝ)/2) :=
      (div_le_div_iff₀ hdL hdR).mpr (mul_le_mul_of_nonneg_left hd (by positivity))
    _ = _ := by ring

theorem t1_double_log_compare (R L : ℝ) (hR : Real.exp 4 ≤ R)
    (hRL : R ≤ L) (hL : L ≤ 4*R) :
    4 ≤ Real.log R ∧ Real.log R ≤ Real.log L ∧
      Real.log (Real.log L) ≤ 2*Real.log (Real.log R) := by
  have hR0 : 0 < R := (Real.exp_pos 4).trans_le hR
  have hL0 : 0 < L := hR0.trans_le hRL
  have hlogR : 4 ≤ Real.log R := by
    rw [← Real.log_exp (4 : ℝ)]
    exact Real.log_le_log (Real.exp_pos 4) hR
  have hlogRL := Real.log_le_log hR0 hRL
  have hlogR0 : 0 < Real.log R := by linarith
  have hlogL0 : 0 < Real.log L := hlogR0.trans_le hlogRL
  have hlogL := Real.log_le_log hL0 hL
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hR0.ne'] at hlogL
  have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have hlogL' : Real.log L ≤ 2*Real.log R := by linarith
  have hloglog := Real.log_le_log hlogL0 hlogL'
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogR0.ne'] at hloglog
  have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show 2 ≤ Real.log R by linarith)
  exact ⟨hlogR,hlogRL,by linarith⟩

theorem t1_primitiveUnconditionalScale_compare (R L : ℝ) (hR : Real.exp 4 ≤ R)
    (hRL : R ≤ L) (hL : L ≤ 4*R) :
    primitiveUnconditionalScale L ≤
      (4*(2 : ℝ)^((1 : ℝ)/10))*primitiveUnconditionalScale R := by
  obtain ⟨hlogR,hlogRL,hloglog⟩ := t1_double_log_compare R L hR hRL hL
  have hR0 := (Real.exp_pos 4).trans_le hR
  have hlogR0 : 0 < Real.log R := by linarith
  have hlogL0 := hlogR0.trans_le hlogRL
  have hllR : 0 ≤ Real.log (Real.log R) := Real.log_nonneg (by linarith)
  have hllL : 0 ≤ Real.log (Real.log L) := Real.log_nonneg (by linarith)
  let a : ℝ := (1 : ℝ)/10
  let b : ℝ := (3 : ℝ)/10
  have hnum := Real.rpow_le_rpow hllL hloglog (show 0 ≤ a by norm_num [a])
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hllR] at hnum
  have hd := Real.rpow_le_rpow hlogR0.le hlogRL (show 0 ≤ b by norm_num [b])
  have hdR := Real.rpow_pos_of_pos hlogR0 b
  have hdL := Real.rpow_pos_of_pos hlogL0 b
  have hn : L*(Real.log (Real.log L))^a ≤
      4*R*((2 : ℝ)^a*(Real.log (Real.log R))^a) :=
    mul_le_mul hL hnum (Real.rpow_nonneg hllL _) (by positivity)
  change L*(Real.log (Real.log L))^a/(Real.log L)^b ≤
    (4*(2 : ℝ)^a)*(R*(Real.log (Real.log R))^a/(Real.log R)^b)
  calc
    _ ≤ (4*R*((2 : ℝ)^a*(Real.log (Real.log R))^a))/(Real.log L)^b :=
      div_le_div_of_nonneg_right hn hdL.le
    _ ≤ (4*R*((2 : ℝ)^a*(Real.log (Real.log R))^a))/(Real.log R)^b :=
      (div_le_div_iff₀ hdL hdR).mpr (mul_le_mul_of_nonneg_left hd
        (mul_nonneg (by positivity) (mul_nonneg (by positivity) (Real.rpow_nonneg hllR _))))
    _ = _ := by ring

end Markov
