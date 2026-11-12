import Markov.IntegerPeriodCircleDescent

noncomputable section
open Set
universe u
namespace Markov

/-- An actual exact integer-period point equality criterion implies
injectivity on every open interval of one positive period. -/
theorem integerPeriodEquality_injOn_Ioo
    {X : Type u} (L : ℝ) (hL : 0 < L) (γ : ℝ → X)
    (heq : ∀ s t : ℝ, γ s = γ t ↔ ∃ n : ℤ, s - t = (n : ℝ) * L)
    (a : ℝ) : Set.InjOn γ (Ioo a (a + L)) := by
  intro s hs t ht hst
  obtain ⟨n, hn⟩ := (heq s t).mp hst
  have hnlo : (-1 : ℝ) < (n : ℝ) := by nlinarith only [hs.1, ht.2, hn, hL]
  have hnhi : (n : ℝ) < 1 := by nlinarith only [hs.2, ht.1, hn, hL]
  have hnlo' : (-1 : ℤ) < n := by exact_mod_cast hnlo
  have hnhi' : n < (1 : ℤ) := by exact_mod_cast hnhi
  have hnzero : n = 0 := by omega
  rw [hnzero] at hn
  simpa only [Int.cast_zero, zero_mul, sub_eq_zero] using hn

end Markov
