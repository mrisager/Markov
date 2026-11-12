import Mathlib.NumberTheory.Chebyshev

/-! A square-root bound for the actual mass of proper prime powers.
Separating exponent two lets the existing logarithmic bound be replaced
by a fixed constant using the third-power envelope for the remaining terms. -/
noncomputable section
open Finset
namespace Markov

theorem t1_chebyshev_prime_power_tail {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x-Chebyshev.theta x ≤ 18*Real.sqrt x := by
  have hx0 := zero_lt_one.trans_le hx
  by_cases h2 : 2 ≤ x
  swap
  · rw [Chebyshev.psi_eq_zero_of_lt_two (lt_of_not_ge h2),
      Chebyshev.theta_eq_zero_of_lt_two (lt_of_not_ge h2),sub_zero]
    positivity
  let D := ⌊Real.log x/Real.log 2⌋₊
  have hlog0 := Real.log_pos (show (1 : ℝ)<2 by norm_num)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hD : (D : ℝ) ≤ Real.log x/Real.log 2 := Nat.floor_le (div_nonneg hlogx hlog0.le)
  rw [Chebyshev.psi_eq_theta_add_sum_theta h2,add_sub_cancel_left]
  change (∑ n ∈ Finset.Icc 2 D, Chebyshev.theta (x^(1/(n : ℝ)))) ≤ _
  by_cases hD2 : 2 ≤ D
  swap
  · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hD2),Finset.sum_empty]
    positivity
  rw [← Finset.add_sum_Ioc_eq_sum_Icc hD2]
  have hfirst : Chebyshev.theta (x^((1 : ℝ)/2)) ≤ Real.log 4*Real.sqrt x := by
    rw [← Real.sqrt_eq_rpow]
    exact Chebyshev.theta_le_log4_mul_x (Real.sqrt_nonneg _)
  have hrest : (∑ n ∈ Finset.Ioc 2 D, Chebyshev.theta (x^(1/(n : ℝ)))) ≤
      (D : ℝ)*(Real.log 4*x^((1 : ℝ)/3)) := by
    calc
      _ ≤ ∑ _n ∈ Finset.Ioc 2 D, Real.log 4*x^((1 : ℝ)/3) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' : (3 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_Ioc.mp hn).1
        have hp := Real.rpow_le_rpow_of_exponent_le hx
          (one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<3) hn')
        exact (Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg hx0.le _)).trans
          (mul_le_mul_of_nonneg_left hp (Real.log_nonneg (by norm_num)))
      _ = ((Finset.Ioc 2 D).card : ℝ)*(Real.log 4*x^((1 : ℝ)/3)) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by rw [Nat.card_Ioc]; exact_mod_cast Nat.sub_le D 2) (by positivity)
  have hlog4 : Real.log 4 = 2*Real.log 2 := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  have haux : Real.log x ≤ 6*x^((1 : ℝ)/6) := calc
    _ ≤ x^((1 : ℝ)/6)/((1 : ℝ)/6) := Real.log_le_rpow_div hx0.le (by norm_num)
    _ = _ := by ring
  have hR : (D : ℝ)*(Real.log 4*x^((1 : ℝ)/3)) ≤ 12*Real.sqrt x := calc
    _ ≤ (Real.log x/Real.log 2)*(Real.log 4*x^((1 : ℝ)/3)) :=
      mul_le_mul_of_nonneg_right hD (by positivity)
    _ = 2*Real.log x*x^((1 : ℝ)/3) := by rw [hlog4]; field_simp
    _ ≤ 2*(6*x^((1 : ℝ)/6))*x^((1 : ℝ)/3) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haux (by norm_num)) (by positivity)
    _ = 12*Real.sqrt x := by
      rw [Real.sqrt_eq_rpow,show (1 : ℝ)/2 = 1/6+1/3 by norm_num,Real.rpow_add hx0]
      ring
  have hF : Real.log 4*Real.sqrt x ≤ 6*Real.sqrt x := by
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<4)]
  calc
    _ ≤ 6*Real.sqrt x+12*Real.sqrt x := add_le_add (hfirst.trans hF) (hrest.trans hR)
    _ = _ := by ring

end Markov
