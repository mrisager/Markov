import T1RieszKernelInversion
import T1MertensFinite

/-! The actual finite Riesz mean of the Möbius function, and its exact
representation by the normalized continuous weights. -/
noncomputable section
open Complex Finset ArithmeticFunction
open scoped Moebius Nat
namespace Markov

def t1_rieszMertens (k : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n : ℝ)*(max (x-(n : ℝ)) 0)^k/(k ! : ℝ)

def t1_moebiusKernelTerm (k : ℕ) (x : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else (μ n : ℂ)*t1_rieszKernel k ((n : ℝ)/x)

theorem t1_moebiusKernelTerm_vanishes {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : n ∉ Finset.Icc 1 ⌊x⌋₊) : t1_moebiusKernelTerm k x n = 0 := by
  by_cases h0 : n = 0
  · rw [t1_moebiusKernelTerm,if_pos h0]
  · have hnx : x < (n : ℝ) := by
      by_contra! hnle
      exact hn (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr h0,Nat.le_floor hnle⟩)
    have hr : 1 ≤ (n : ℝ)/x := (le_div_iff₀ hx).mpr (by simpa only [one_mul] using hnx.le)
    rw [t1_moebiusKernelTerm,if_neg h0,t1_rieszKernel,max_eq_right (sub_nonpos.mpr hr),
      Complex.ofReal_zero,zero_pow hk.ne',zero_div,mul_zero]

theorem t1_rieszMertens_eq_tsum {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : 0 < x) :
    (t1_rieszMertens k x : ℂ) =
      (x : ℂ)^k*(∑' n, t1_moebiusKernelTerm k x n) := by
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun _ hn => t1_moebiusKernelTerm_vanishes hk hx hn),
    Finset.mul_sum,t1_rieszMertens]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨h1,h2⟩ := Finset.mem_Icc.mp hn
  have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp h2
  have hdiv : (n : ℝ)/x ≤ 1 := (div_le_iff₀ hx).mpr (by simpa only [one_mul] using hnx)
  have h0 : n ≠ 0 := Nat.ne_zero_of_lt h1
  simp only [t1_moebiusKernelTerm,if_neg h0,t1_rieszKernel,
    max_eq_left (sub_nonneg.mpr hnx),max_eq_left (sub_nonneg.mpr hdiv)]
  push_cast
  have hxC := Complex.ofReal_ne_zero.mpr hx.ne'
  have hEq : (1-(n : ℂ)/(x : ℂ)) = ((x : ℂ)-(n : ℂ))/(x : ℂ) := by field_simp
  rw [hEq,div_pow]
  field_simp [hxC]

end Markov
