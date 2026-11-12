import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Choose.Factorization

/-!
Elementary Chebyshev lower bound on the pinned library. The finite
prime-power decomposition of psi follows the corresponding Mathlib
proof at d13f23b723b8a846827a245b89c10fc7d3f11612 (Apache 2.0).
The binomial argument uses the explicit prime product.
-/
noncomputable section
open Finset Nat ArithmeticFunction
namespace Markov

def t1_primesLE (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter Nat.Prime

theorem t1_mem_primesLE {n p : ℕ} : p ∈ t1_primesLE n ↔ p ≤ n ∧ p.Prime := by
  simp only [t1_primesLE,mem_filter,mem_Icc]
  exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨h.2.one_le,h.1⟩,h.2⟩⟩

theorem t1_prime_of_mem_primesLE {n p : ℕ} (hp : p ∈ t1_primesLE n) : p.Prime :=
  (t1_mem_primesLE.mp hp).2

theorem t1_primesLE_mono {m n : ℕ} (h : m ≤ n) : t1_primesLE m ⊆ t1_primesLE n := by
  intro p hp
  obtain ⟨hpm,hP⟩ := t1_mem_primesLE.mp hp
  exact t1_mem_primesLE.mpr ⟨hpm.trans h,hP⟩

theorem t1_chebyshev_psi_eq_sum_prime_logs (n : ℕ) :
    Chebyshev.psi n = ∑ p ∈ t1_primesLE n, (p.log n : ℝ)*Real.log p := by
  let P := (Finset.Icc 1 n).filter Nat.Prime
  have hP : P = t1_primesLE n := rfl
  let B := fun p : ℕ => (Finset.Icc 1 (p.log n)).image (p ^ ·)
  calc
    _ = ∑ m ∈ Finset.Icc 1 n, vonMangoldt m := by
      simp [Chebyshev.psi, ← Icc_add_one_left_eq_Ioc]
    _ = ∑ m ∈ P.biUnion B, vonMangoldt m := by
      refine (sum_subset (fun q hq => ?_) fun x hx hnot => ?_).symm
      · simp only [P,B,mem_biUnion,mem_filter,mem_Icc,mem_image] at hq ⊢
        obtain ⟨p,⟨_,hp⟩,k,⟨_,hk⟩,rfl⟩ := hq
        have hn0 : n ≠ 0 := by omega
        exact ⟨one_le_pow₀ hp.one_le,pow_le_of_le_log hn0 hk⟩
      · by_contra hzero
        have hpp := (vonMangoldt_ne_zero_iff).mp hzero
        obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff x).mp hpp
        have hx' := mem_Icc.mp hx
        have hpn : p ≤ n := (le_of_dvd (Nat.pow_pos hp.pos)
          (dvd_pow_self p hk.ne')).trans hx'.2
        apply hnot
        refine mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.one_le,hpn⟩,hp⟩,?_⟩
        exact mem_image.mpr ⟨k,mem_Icc.mpr ⟨hk,le_log_of_pow_le hp.one_lt hx'.2⟩,rfl⟩
    _ = ∑ p ∈ P, ∑ q ∈ B p, vonMangoldt q := by
      rw [sum_biUnion]
      intro p hp q hq hpq
      apply Finset.disjoint_left.mpr
      intro a hap haq
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hap
      obtain ⟨l,hl,he⟩ := mem_image.mp haq
      exact hpq (Nat.Prime.pow_inj' (t1_prime_of_mem_primesLE hp) (t1_prime_of_mem_primesLE hq)
        (Nat.ne_zero_of_lt (mem_Icc.mp hk).1) (Nat.ne_zero_of_lt (mem_Icc.mp hl).1) he.symm).1
    _ = ∑ p ∈ t1_primesLE n, ∑ k ∈ Finset.Icc 1 (p.log n), vonMangoldt (p^k) := by
      rw [hP]
      apply sum_congr rfl
      intro p hp
      exact sum_image fun _ _ _ _ he =>
        Nat.pow_right_injective (t1_prime_of_mem_primesLE hp).two_le he
    _ = ∑ p ∈ t1_primesLE n, ∑ _k ∈ Finset.Icc 1 (p.log n), Real.log p := by
      apply sum_congr rfl
      intro p hp
      apply sum_congr rfl
      intro k hk
      rw [vonMangoldt_apply_pow (Nat.ne_zero_of_lt (mem_Icc.mp hk).1),
        vonMangoldt_apply_prime (t1_prime_of_mem_primesLE hp)]
    _ = _ := by simp

def t1_chebyshevPrimeProduct (n : ℕ) : ℕ :=
  ∏ p ∈ t1_primesLE n, p^(p.log n)

theorem t1_chebyshevPrimeProduct_ne_zero (n : ℕ) :
    t1_chebyshevPrimeProduct n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp => pow_ne_zero _ (t1_prime_of_mem_primesLE hp).ne_zero

theorem t1_choose_dvd_chebyshevPrimeProduct {n k : ℕ} (hk : k ≤ n) :
    n.choose k ∣ t1_chebyshevPrimeProduct n := by
  rw [← Nat.factorization_prime_le_iff_dvd (Nat.choose_ne_zero hk) (t1_chebyshevPrimeProduct_ne_zero n)]
  intro p hp
  apply Nat.factorization_choose_le_log.trans
  by_cases hn : p ≤ n
  · unfold t1_chebyshevPrimeProduct
    rw [Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (t1_prime_of_mem_primesLE hq).ne_zero)]
    calc
      _ = (p^(p.log n)).factorization p := (Nat.factorization_pow_self hp).symm
      _ ≤ _ := Finset.single_le_sum (f := fun q => (q^(q.log n)).factorization p)
        (fun _ _ => Nat.zero_le _) (t1_mem_primesLE.mpr ⟨hn,hp⟩)
  · rw [Nat.log_of_lt (lt_of_not_ge hn)]
    exact Nat.zero_le _

theorem t1_chebyshevPsi_ge_nat (n : ℕ) :
    (n : ℝ)*Real.log 2-Real.log ((n : ℝ)+1) ≤ Chebyshev.psi n := by
  have hD := t1_chebyshevPrimeProduct_ne_zero n
  have hPow : 2^n ≤ (n+1)*t1_chebyshevPrimeProduct n := calc
    _ = ∑ k ∈ Finset.range (n+1), n.choose k := (Nat.sum_range_choose n).symm
    _ ≤ ∑ _k ∈ Finset.range (n+1), t1_chebyshevPrimeProduct n :=
      Finset.sum_le_sum fun k hk => Nat.le_of_dvd (Nat.pos_of_ne_zero hD)
        (t1_choose_dvd_chebyshevPrimeProduct (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    _ = _ := by simp
  have hψ : Chebyshev.psi n = Real.log (t1_chebyshevPrimeProduct n : ℝ) := by
    rw [t1_chebyshevPrimeProduct,Nat.cast_prod,Real.log_prod]
    · simp only [Nat.cast_pow,Real.log_pow,t1_chebyshev_psi_eq_sum_prime_logs]
    · intro p hp
      exact_mod_cast (pow_ne_zero (p.log n) (t1_prime_of_mem_primesLE hp).ne_zero)
  have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ)^n)
    (show (2 : ℝ)^n ≤ ((n : ℝ)+1)*(t1_chebyshevPrimeProduct n : ℝ) by exact_mod_cast hPow)
  rw [Real.log_pow,Real.log_mul (by positivity) (by exact_mod_cast hD),← hψ] at hl
  linarith

theorem t1_chebyshevPsi_ge {x : ℝ} (hx : 0 ≤ x) :
    (x-1)*Real.log 2-Real.log (x+2) ≤ Chebyshev.psi x := by
  have hψ : Chebyshev.psi x = Chebyshev.psi (⌊x⌋₊ : ℝ) := by simp [Chebyshev.psi]
  have hn : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hN : x-1 ≤ (⌊x⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one x]
  have hl := Real.log_le_log (by positivity : 0 < (⌊x⌋₊ : ℝ)+1) (by linarith : (⌊x⌋₊ : ℝ)+1 ≤ x+2)
  rw [hψ]
  exact (sub_le_sub (mul_le_mul_of_nonneg_right hN (Real.log_nonneg (by norm_num))) hl).trans
    (t1_chebyshevPsi_ge_nat ⌊x⌋₊)

end Markov
