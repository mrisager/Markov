import T1PrimitiveErrorScales
import T1LengthAsymptotics

/-! Both actual paper error scales eventually dominate the constant error
from the exceptional orbits and bounded squared-length correction. -/
noncomputable section
open Filter Asymptotics
namespace Markov

theorem t1_primitiveConditionalScale_eventually_ge_one :
    ∀ᶠ R : ℝ in atTop, 1 ≤ primitiveConditionalScale R := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop ((1 : ℝ)/2)
    (show (0 : ℝ) < 1 by norm_num)).bound (c := 1) (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ),hsmall] with R hR hsmallR
  have hR0 : 0 < R := by linarith
  have hd := Real.rpow_pos_of_pos (Real.log_pos hR) ((1 : ℝ)/2)
  have hl : (Real.log R)^((1 : ℝ)/2) ≤ R := by
    simpa only [Real.norm_eq_abs,abs_of_pos hd,Real.rpow_one,abs_of_pos hR0,one_mul]
      using hsmallR
  change 1 ≤ R/(Real.log R)^((1 : ℝ)/2)
  exact (le_div_iff₀ hd).mpr (by simpa only [one_mul] using hl)

theorem t1_primitiveUnconditionalScale_eventually_ge_one :
    ∀ᶠ R : ℝ in atTop, 1 ≤ primitiveUnconditionalScale R := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop ((3 : ℝ)/10)
    (show (0 : ℝ) < 1 by norm_num)).bound (c := 1) (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ),hsmall,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
    with R hR hsmallR hll
  have hR0 : 0 < R := by linarith
  have hd := Real.rpow_pos_of_pos (Real.log_pos hR) ((3 : ℝ)/10)
  have hl : (Real.log R)^((3 : ℝ)/10) ≤ R := by
    simpa only [Real.norm_eq_abs,abs_of_pos hd,Real.rpow_one,abs_of_pos hR0,one_mul]
      using hsmallR
  have hn := Real.one_le_rpow hll (by norm_num : (0 : ℝ) ≤ (1 : ℝ)/10)
  have hnum : R ≤ R*(Real.log (Real.log R))^((1 : ℝ)/10) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hR0.le
  change 1 ≤ R*(Real.log (Real.log R))^((1 : ℝ)/10)/(Real.log R)^((3 : ℝ)/10)
  exact (le_div_iff₀ hd).mpr (by simpa only [one_mul] using hl.trans hnum)

theorem t1_one_isBigO_conditionalScale :
    (fun _ : ℝ => (1 : ℝ)) =O[atTop] conditionalScale := by
  apply IsBigO.of_bound 1
  filter_upwards [Real.tendsto_log_atTop.eventually t1_primitiveConditionalScale_eventually_ge_one]
    with x hx
  have h : 1 ≤ conditionalScale x := hx
  have hp : 0 ≤ conditionalScale x := zero_le_one.trans h
  simpa only [norm_one,Real.norm_eq_abs,abs_of_nonneg hp,one_mul] using h

theorem t1_one_isBigO_unconditionalScale :
    (fun _ : ℝ => (1 : ℝ)) =O[atTop] unconditionalScale := by
  apply IsBigO.of_bound 1
  filter_upwards [Real.tendsto_log_atTop.eventually t1_primitiveUnconditionalScale_eventually_ge_one]
    with x hx
  have h : 1 ≤ unconditionalScale x := hx
  have hp : 0 ≤ unconditionalScale x := zero_le_one.trans h
  simpa only [norm_one,Real.norm_eq_abs,abs_of_nonneg hp,one_mul] using h

end Markov
