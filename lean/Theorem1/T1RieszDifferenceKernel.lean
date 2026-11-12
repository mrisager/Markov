import T1RieszMertensSum
import Mathlib.Algebra.Group.ForwardDiff

/-! The finite-difference weight used to recover the unsmoothed sum. -/
noncomputable section
open Finset
open scoped fwdDiff Nat
namespace Markov

def t1_differenceWeight (k j : ℕ) : ℝ := (-1 : ℝ)^(k-j)*(k.choose j : ℝ)

def t1_rieszDifference (k : ℕ) (x h : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), t1_differenceWeight k j*t1_rieszMertens k (x+(j : ℝ)*h)

def t1_rieszDifferenceKernel (k : ℕ) (x h : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k+1),
    t1_differenceWeight k j*(max (x+(j : ℝ)*h-(n : ℝ)) 0)^k/(k ! : ℝ)

theorem t1_differenceWeight_abs (k j : ℕ) : |t1_differenceWeight k j| = k.choose j := by
  simp [t1_differenceWeight,abs_mul,abs_pow]

theorem t1_difference_polynomial_moment (k : ℕ) (y : ℝ) :
    ∑ j ∈ Finset.range (k+1), t1_differenceWeight k j*(y+(j : ℝ))^k = (k ! : ℝ) := by
  have he := congrFun (fwdDiff_iter_eq_factorial (R := ℝ) (n := k)) y
  rw [fwdDiff_iter_eq_sum_shift] at he
  simpa only [zsmul_eq_mul,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,
    Int.cast_natCast,nsmul_eq_mul,mul_one,Pi.natCast_apply,t1_differenceWeight] using he

theorem t1_rieszDifferenceKernel_eq_pow {k n : ℕ} {x h : ℝ} (hh : 0 < h)
    (hn : (n : ℝ) ≤ x) :
    t1_rieszDifferenceKernel k x h n = h^k := by
  let y := (x-(n : ℝ))/h
  have he (j : ℕ) : x+(j : ℝ)*h-(n : ℝ) = h*(y+(j : ℝ)) := by
    dsimp [y]
    field_simp [hh.ne']
    ring
  have hf : (k ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  unfold t1_rieszDifferenceKernel
  calc
    _ = ∑ j ∈ Finset.range (k+1),
        (h^k/(k ! : ℝ))*(t1_differenceWeight k j*(y+(j : ℝ))^k) := by
      apply Finset.sum_congr rfl
      intro j _
      have hn0 : 0 ≤ x+(j : ℝ)*h-(n : ℝ) :=
        sub_nonneg.mpr (hn.trans (le_add_of_nonneg_right (by positivity)))
      rw [max_eq_left hn0,he,mul_pow]
      ring
    _ = _ := by
      rw [← Finset.mul_sum,t1_difference_polynomial_moment]
      exact div_mul_cancel₀ _ hf

end Markov
