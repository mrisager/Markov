import Markov.PrimitiveRayDecomposition
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-! Finite Möbius inversion for actual signed integer vectors.
No asymptotic cancellation estimate is assumed or asserted here. -/

noncomputable section
open Classical Finset
open scoped ArithmeticFunction.Moebius

namespace Markov

theorem t1_moebius_divisor_sum (n : ℕ) :
    (∑ g ∈ n.divisors, μ g) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] using h

/-- The gcd-divisor Möbius sum is exactly the primitive-vector indicator,
including the correct zero value at the zero vector. -/
theorem t1_primitive_indicator_moebius (p : ℤ × ℤ) :
    (∑ g ∈ (Int.gcd p.1 p.2).divisors, μ g) =
      if IsCoprime p.1 p.2 then 1 else 0 := by
  simpa only [Int.isCoprime_iff_gcd_eq_one] using
    t1_moebius_divisor_sum (Int.gcd p.1 p.2)

/-- Exact finite primitive count before changing the order of summation. -/
theorem t1_finite_primitive_count_moebius (S : Finset (ℤ × ℤ)) :
    ((S.filter (fun p => IsCoprime p.1 p.2)).card : ℤ) =
      ∑ p ∈ S, ∑ g ∈ (Int.gcd p.1 p.2).divisors, μ g := by
  simp_rw [t1_primitive_indicator_moebius]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A concrete finite divisor cutoff extracted from the actual vectors. -/
def t1_gcdCutoff (S : Finset (ℤ × ℤ)) : ℕ :=
  S.sup (fun p => Int.gcd p.1 p.2)

theorem t1_gcd_le_cutoff (S : Finset (ℤ × ℤ)) {p : ℤ × ℤ} (hp : p ∈ S) :
    Int.gcd p.1 p.2 ≤ t1_gcdCutoff S :=
  Finset.le_sup (f := fun p => Int.gcd p.1 p.2) hp

theorem t1_gcd_divisors_as_filter (S : Finset (ℤ × ℤ)) {p : ℤ × ℤ}
    (hp : p ∈ S) (hn : p ≠ (0, 0)) :
    (Int.gcd p.1 p.2).divisors =
      (Finset.Icc 1 (t1_gcdCutoff S)).filter (fun g => g ∣ Int.gcd p.1 p.2) := by
  have hpos := integerPair_gcd_pos hn
  ext g
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hgd, _⟩
    have hgle := Nat.le_of_dvd hpos hgd
    have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgd hpos
    exact ⟨⟨hgpos, hgle.trans (t1_gcd_le_cutoff S hp)⟩, hgd⟩
  · rintro ⟨_, hgd⟩
    exact ⟨hgd, hpos.ne'⟩

/-- Actual finite interchange: primitive vectors are counted by Möbius
weights times the cardinalities of their common-divisor fibers. The cutoff
is computed from S itself and the zero vector is explicitly excluded. -/
theorem t1_finite_primitive_count_divisor_fibers (S : Finset (ℤ × ℤ))
    (hS : ∀ p ∈ S, p ≠ (0, 0)) :
    ((S.filter (fun p => IsCoprime p.1 p.2)).card : ℤ) =
      ∑ g ∈ Finset.Icc 1 (t1_gcdCutoff S),
        μ g * ((S.filter (fun p => g ∣ Int.gcd p.1 p.2)).card : ℤ) := by
  rw [t1_finite_primitive_count_moebius]
  calc
    _ = ∑ p ∈ S, ∑ g ∈ Finset.Icc 1 (t1_gcdCutoff S),
          if g ∣ Int.gcd p.1 p.2 then μ g else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [t1_gcd_divisors_as_filter S hp (hS p hp), Finset.sum_filter]
    _ = ∑ g ∈ Finset.Icc 1 (t1_gcdCutoff S),
          ∑ p ∈ S, if g ∣ Int.gcd p.1 p.2 then μ g else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_comm _ _

end Markov
