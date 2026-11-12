import T1VKRieszGrowth
import T1RieszDifferenceError

/-! Desmooth the genuine VK Riesz estimate, preserving the classical
logarithmic exponents in the ordinary Mertens sum. -/
noncomputable section
open Filter Asymptotics Finset
namespace Markov

theorem t1_rieszDifference_vk_bound {k : ℕ} {K d x h : ℝ}
    (hK : 0 ≤ K) (hd : 0 < d) (hx : t1_vkHeightBase ≤ x)
    (hh : 0 ≤ h) (hhx : h ≤ x)
    (hR : ∀ y : ℝ, x ≤ y → |t1_rieszMertens k y| ≤
      K*y^(k+1)*Real.exp (-d*t1_vkWeight y)) :
    |t1_rieszDifference k x h| ≤
      (t1_differenceWeightNorm k*K*(1+(k : ℝ))^(k+1))*
        (x^(k+1)*Real.exp (-d*t1_vkWeight x)) := by
  have hx0 := (Real.exp_pos (Real.exp 1)).trans_le hx
  unfold t1_rieszDifference
  calc
    _ ≤ ∑ j ∈ Finset.range (k+1), |t1_differenceWeight k j*t1_rieszMertens k (x+(j : ℝ)*h)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (k+1), |t1_differenceWeight k j| *
        (K*((1+(k : ℝ))*x)^(k+1)*Real.exp (-d*t1_vkWeight x)) := by
      apply Finset.sum_le_sum
      intro j hj
      let y := x+(j : ℝ)*h
      have hj' : (j : ℝ) ≤ k := by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hj)
      have hy : x ≤ y := le_add_of_nonneg_right (by positivity)
      have hy0 := hx0.trans_le hy
      have hyx : y ≤ (1+(k : ℝ))*x := by
        dsimp [y]
        linarith [mul_le_mul hj' hhx hh (Nat.cast_nonneg (α := ℝ) k)]
      have hw := t1_vkWeight_monotone hx (hx.trans hy) hy
      have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hw (neg_nonpos.mpr hd.le))
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (hR y hy).trans (mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy0.le hyx _) hK) he
        (Real.exp_pos _).le (by positivity))
    _ = _ := by
      rw [← Finset.sum_mul,← t1_differenceWeightNorm,mul_pow]
      ring

theorem t1_mertens_le_difference_div_add_error {k : ℕ} (hk : 0 < k)
    {x h : ℝ} (hx : 0 ≤ x) (hh : 1 ≤ h) :
    |t1_mertens x| ≤ |t1_rieszDifference k x h| / h^k+
      t1_differenceBoundaryConstant k*((k : ℝ)+1)*h := by
  let D := t1_rieszDifference k x h
  let M := t1_mertens x
  let B := t1_differenceBoundaryConstant k
  have hh0 := zero_lt_one.trans_le hh
  have hhK := pow_pos hh0 k
  have hE : |D-h^k*M| ≤ B*h^k*((k : ℝ)*h+1) := t1_rieszDifference_error hk hx hh0
  have htri : |M| * h^k ≤ |D|+|D-h^k*M| := by
    nth_rw 1 [← abs_of_pos hhK]
    rw [← abs_mul]
    have he : M*h^k = D-(D-h^k*M) := by ring
    rw [he]
    simpa only [Real.norm_eq_abs] using norm_sub_le D (D-h^k*M)
  have hB := t1_differenceBoundaryConstant_nonneg k
  calc
    _ ≤ (|D|+B*h^k*((k : ℝ)*h+1))/h^k :=
      (le_div_iff₀ hhK).mpr (htri.trans (add_le_add_right hE _))
    _ = |D| / h^k+B*((k : ℝ)*h+1) := by field_simp [hhK.ne']
    _ ≤ _ := by
      apply add_le_add_right
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith) hB

def t1_vkDesmoothingStep (k : ℕ) (d x : ℝ) : ℝ :=
  x*Real.exp (-(d/((k : ℝ)+1))*t1_vkWeight x)

theorem t1_vkDesmoothingStep_eventual_bounds (k : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ t1_vkDesmoothingStep k d x ∧ t1_vkDesmoothingStep k d x ≤ x := by
  let b := d/((k : ℝ)+1)
  have hb : 0 < b := by dsimp [b]; positivity
  have hsmall := t1_vkWeight_isLittleO_log.bound (c := 1/b) (by positivity)
  filter_upwards [eventually_gt_atTop (Real.exp 1),hsmall] with x hx hsmallx
  have hx0 := (Real.exp_pos _).trans hx
  have hl : 0 < Real.log x := (by norm_num : (0 : ℝ)<1).trans
    ((Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos _) hx))
  have hw := t1_vkWeight_pos x hx
  have hW : b*t1_vkWeight x ≤ Real.log x := by
    have h : t1_vkWeight x ≤ (1/b)*Real.log x := by
      simpa only [Real.norm_eq_abs,abs_of_pos hw,abs_of_pos hl] using hsmallx
    have he : (1/b)*Real.log x = Real.log x/b := by ring
    rw [he] at h
    simpa only [mul_comm] using (le_div_iff₀ hb).mp h
  change 1 ≤ x*Real.exp (-b*t1_vkWeight x) ∧ x*Real.exp (-b*t1_vkWeight x) ≤ x
  constructor
  · nth_rw 1 [← Real.exp_log hx0]
    rw [← Real.exp_add]
    calc
      1 = Real.exp 0 := Real.exp_zero.symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  · exact mul_le_of_le_one_right hx0.le (Real.exp_le_one_iff.mpr (by rw [neg_mul]; exact neg_nonpos.mpr (mul_nonneg hb.le hw.le)))

theorem t1_vkDesmoothingStep_power (k : ℕ) (d x : ℝ) :
    (t1_vkDesmoothingStep k d x)^(k+1) = x^(k+1)*Real.exp (-d*t1_vkWeight x) := by
  rw [t1_vkDesmoothingStep,mul_pow,← Real.exp_nat_mul,Nat.cast_add,Nat.cast_one]
  congr 2
  field_simp

end Markov
