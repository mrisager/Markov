import T1RieszDifferenceKernel

/-! Put the finite differences at a common cutoff, then split exactly
into the genuine Mertens sum and a short boundary interval. -/
noncomputable section
open Finset ArithmeticFunction
open scoped Moebius Nat
namespace Markov

theorem t1_rieszMertens_extend_sum {k N : ℕ} (hk : 0 < k) {y : ℝ} (hy : 0 ≤ y)
    (hN : ⌊y⌋₊ ≤ N) :
    t1_rieszMertens k y = ∑ n ∈ Finset.Icc 1 N, (μ n : ℝ)*(max (y-(n : ℝ)) 0)^k/(k ! : ℝ) := by
  unfold t1_rieszMertens
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right hN)
  intro n hn hnot
  have hn' : ⌊y⌋₊ < n := by
    by_contra! he
    exact hnot (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,he⟩)
  have hy' : y < (n : ℝ) := (Nat.floor_lt hy).mp hn'
  rw [max_eq_right (sub_nonpos.mpr hy'.le),zero_pow hk.ne',mul_zero,zero_div]

theorem t1_rieszDifference_eq_sum {k : ℕ} (hk : 0 < k) {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) :
    t1_rieszDifference k x h =
      ∑ n ∈ Finset.Icc 1 ⌊x+(k : ℝ)*h⌋₊, (μ n : ℝ)*t1_rieszDifferenceKernel k x h n := by
  unfold t1_rieszDifference t1_rieszDifferenceKernel
  calc
    _ = ∑ j ∈ Finset.range (k+1), ∑ n ∈ Finset.Icc 1 ⌊x+(k : ℝ)*h⌋₊,
        (μ n : ℝ)*(t1_differenceWeight k j*(max (x+(j : ℝ)*h-(n : ℝ)) 0)^k/(k ! : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : (j : ℝ) ≤ k := by
        exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hprod := mul_le_mul_of_nonneg_right hj' hh
      rw [t1_rieszMertens_extend_sum hk (by positivity)
        (Nat.floor_mono (add_le_add_right hprod x)),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = _ := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]

theorem t1_rieszDifference_split {k : ℕ} (hk : 0 < k) {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h) :
    t1_rieszDifference k x h =
      h^k*t1_mertens x +
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x+(k : ℝ)*h⌋₊, (μ n : ℝ)*t1_rieszDifferenceKernel k x h n := by
  rw [t1_rieszDifference_eq_sum hk hx hh.le]
  let D := ⌊x⌋₊
  let N := ⌊x+(k : ℝ)*h⌋₊
  have hDN : D ≤ N := Nat.floor_mono (le_add_of_nonneg_right (by positivity))
  have hI : Finset.Icc 1 D ∪ Finset.Ioc D N = Finset.Icc 1 N := by
    ext n
    simp only [mem_union,mem_Icc,mem_Ioc]
    omega
  have hd : Disjoint (Finset.Icc 1 D) (Finset.Ioc D N) := by
    apply Finset.disjoint_left.mpr
    intro n hD hN
    exact (mem_Ioc.mp hN).1.not_ge (mem_Icc.mp hD).2
  change (∑ n ∈ Finset.Icc 1 N, _) = _
  rw [← hI,Finset.sum_union hd]
  congr 1
  rw [t1_mertens,t1_mertensNat,Int.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [t1_rieszDifferenceKernel_eq_pow hh ((Nat.le_floor_iff hx).mp (mem_Icc.mp hn).2),
    mul_comm]

end Markov
