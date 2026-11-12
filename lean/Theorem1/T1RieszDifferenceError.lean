import T1RieszDifferenceSum

/-! A genuine short-interval error for desmoothing. The only arithmetic
fact used here is the actual bound |μ(n)|≤1. -/
noncomputable section
open Finset ArithmeticFunction
open scoped Moebius Nat
namespace Markov

def t1_differenceWeightNorm (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), |t1_differenceWeight k j|

def t1_differenceBoundaryConstant (k : ℕ) : ℝ :=
  t1_differenceWeightNorm k*(k : ℝ)^k/(k ! : ℝ)

theorem t1_differenceWeightNorm_nonneg (k : ℕ) : 0 ≤ t1_differenceWeightNorm k :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem t1_differenceBoundaryConstant_nonneg (k : ℕ) :
    0 ≤ t1_differenceBoundaryConstant k := by
  unfold t1_differenceBoundaryConstant
  positivity [t1_differenceWeightNorm_nonneg k]

theorem t1_rieszDifferenceKernel_boundary_bound (k n : ℕ) {x h : ℝ} (hh : 0 ≤ h)
    (hn : x < (n : ℝ)) :
    |t1_rieszDifferenceKernel k x h n| ≤ t1_differenceBoundaryConstant k*h^k := by
  have hkh : 0 ≤ (k : ℝ)*h := by positivity
  have hf : 0 < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  unfold t1_rieszDifferenceKernel
  calc
    _ ≤ ∑ j ∈ Finset.range (k+1),
        |t1_differenceWeight k j*(max (x+(j : ℝ)*h-(n : ℝ)) 0)^k/(k ! : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (k+1), |t1_differenceWeight k j| * ((k : ℝ)*h)^k/(k ! : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : (j : ℝ) ≤ k := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hle : max (x+(j : ℝ)*h-(n : ℝ)) 0 ≤ (k : ℝ)*h := by
        apply max_le (by linarith [mul_le_mul_of_nonneg_right hj' hh]) hkh
      have hnon : 0 ≤ max (x+(j : ℝ)*h-(n : ℝ)) 0 := le_max_right _ _
      rw [abs_div,abs_mul,abs_of_nonneg (pow_nonneg hnon _),abs_of_pos hf]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnon hle k) (abs_nonneg _)) hf.le
    _ = _ := by
      simp_rw [mul_div_assoc,← Finset.sum_mul]
      rw [t1_differenceBoundaryConstant,t1_differenceWeightNorm,mul_pow]
      ring

theorem t1_differenceBoundary_card_le (k : ℕ) {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) :
    ((Finset.Ioc ⌊x⌋₊ ⌊x+(k : ℝ)*h⌋₊).card : ℝ) ≤ (k : ℝ)*h+1 := by
  have hN : x ≤ x+(k : ℝ)*h := le_add_of_nonneg_right (by positivity)
  rw [Nat.card_Ioc,Nat.cast_sub (Nat.floor_mono hN)]
  linarith [Nat.floor_le (hx.trans hN),Nat.lt_floor_add_one x]

theorem t1_rieszDifference_error {k : ℕ} (hk : 0 < k) {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h) :
    |t1_rieszDifference k x h-h^k*t1_mertens x| ≤
      t1_differenceBoundaryConstant k*h^k*((k : ℝ)*h+1) := by
  let S := Finset.Ioc ⌊x⌋₊ ⌊x+(k : ℝ)*h⌋₊
  rw [t1_rieszDifference_split hk hx hh,add_sub_cancel_left]
  change |∑ n ∈ S, (μ n : ℝ)*t1_rieszDifferenceKernel k x h n| ≤ _
  have hB := t1_differenceBoundaryConstant_nonneg k
  have hcard := t1_differenceBoundary_card_le k hx hh.le
  calc
    _ ≤ ∑ n ∈ S, |(μ n : ℝ)*t1_rieszDifferenceKernel k x h n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ S, t1_differenceBoundaryConstant k*h^k := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' : x < (n : ℝ) := (Nat.floor_lt hx).mp (mem_Ioc.mp hn).1
      have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) hμ).trans
        (t1_rieszDifferenceKernel_boundary_bound k n hh.le hn')
    _ = (t1_differenceBoundaryConstant k*h^k)*(S.card : ℝ) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcard (by positivity)

end Markov
