import T1RieszDifferenceError

/-! Recover the unsmoothed Möbius sum from an actual Riesz mean bound,
with an explicit tradeoff between the step size and the boundary error. -/
noncomputable section
open Finset
namespace Markov

theorem t1_rieszDifference_bound {k : ℕ} {σ K : ℝ} (hσ : 0 ≤ σ) (hK : 0 ≤ K)
    (hR : ∀ y : ℝ, 1 ≤ y → |t1_rieszMertens k y| ≤ K*y^(σ+(k : ℝ)))
    {x h : ℝ} (hx : 1 ≤ x) (hh : 0 ≤ h) (hhx : h ≤ x) :
    |t1_rieszDifference k x h| ≤
      (t1_differenceWeightNorm k*K*(1+(k : ℝ))^(σ+(k : ℝ)))*x^(σ+(k : ℝ)) := by
  have hx0 := zero_lt_one.trans_le hx
  have hexp : 0 ≤ σ+(k : ℝ) := by positivity
  unfold t1_rieszDifference
  calc
    _ ≤ ∑ j ∈ Finset.range (k+1), |t1_differenceWeight k j*t1_rieszMertens k (x+(j : ℝ)*h)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (k+1), |t1_differenceWeight k j| * (K*((1+(k : ℝ))*x)^(σ+(k : ℝ))) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : (j : ℝ) ≤ k := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hy : 1 ≤ x+(j : ℝ)*h := hx.trans (le_add_of_nonneg_right (by positivity))
      have hxy : x+(j : ℝ)*h ≤ (1+(k : ℝ))*x := by
        have hm := mul_le_mul hj' hhx hh (Nat.cast_nonneg _)
        linarith
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (hR _ hy).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (zero_le_one.trans hy) hxy hexp) hK)
    _ = _ := by
      rw [← Finset.sum_mul,← t1_differenceWeightNorm,Real.mul_rpow (by positivity) hx0.le]
      ring

theorem t1_mertens_desmoothing_bound {k : ℕ} (hk : 0 < k) {σ K : ℝ}
    (hσ : 0 ≤ σ) (hK : 0 ≤ K)
    (hR : ∀ y : ℝ, 1 ≤ y → |t1_rieszMertens k y| ≤ K*y^(σ+(k : ℝ)))
    {x h : ℝ} (hx : 1 ≤ x) (hh : 1 ≤ h) (hhx : h ≤ x) :
    |t1_mertens x| ≤
      (t1_differenceWeightNorm k*K*(1+(k : ℝ))^(σ+(k : ℝ)))*(x^(σ+(k : ℝ))/h^k)
      + t1_differenceBoundaryConstant k*((k : ℝ)+1)*h := by
  let A := t1_differenceWeightNorm k*K*(1+(k : ℝ))^(σ+(k : ℝ))
  let B := t1_differenceBoundaryConstant k
  have hh0 := zero_lt_one.trans_le hh
  have hpow : 0 < h^k := pow_pos hh0 _
  have hR' := t1_rieszDifference_bound hσ hK hR hx hh0.le hhx
  have hE := t1_rieszDifference_error hk (zero_le_one.trans hx) hh0
  have htri : h^k* |t1_mertens x| ≤ |t1_rieszDifference k x h|+
      |t1_rieszDifference k x h-h^k*t1_mertens x| := by
    nth_rw 1 [← abs_of_pos hpow]
    rw [← abs_mul]
    have he : h^k*t1_mertens x =
        t1_rieszDifference k x h-(t1_rieszDifference k x h-h^k*t1_mertens x) := by ring
    nth_rw 1 [he]
    simpa only [Real.norm_eq_abs] using norm_sub_le (t1_rieszDifference k x h)
      (t1_rieszDifference k x h-h^k*t1_mertens x)
  have hb : |t1_mertens x| * h^k ≤ A*x^(σ+(k : ℝ))+B*h^k*((k : ℝ)*h+1) := by
    rw [mul_comm]
    exact htri.trans (add_le_add hR' hE)
  calc
    _ ≤ (A*x^(σ+(k : ℝ))+B*h^k*((k : ℝ)*h+1))/h^k := (le_div_iff₀ hpow).2 hb
    _ = A*(x^(σ+(k : ℝ))/h^k)+B*((k : ℝ)*h+1) := by
      field_simp [hpow.ne']
    _ ≤ _ := by
      apply add_le_add_right
      have hB := t1_differenceBoundaryConstant_nonneg k
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith) hB

end Markov
