import T1MobiusFinite

/-! The genuine summatory Möbius function and exact finite hyperbola
interchange. No asymptotic or cancellation estimate is asserted here. -/

noncomputable section
open Classical Finset
open scoped ArithmeticFunction.Moebius
namespace Markov

def t1_mertensNat (n : ℕ) : ℤ := ∑ g ∈ Finset.Icc 1 n, μ g

def t1_mertens (x : ℝ) : ℝ := (t1_mertensNat ⌊x⌋₊ : ℝ)

theorem t1_mertensNat_zero : t1_mertensNat 0 = 0 := by
  simp [t1_mertensNat]

theorem t1_mertens_interval (D N : ℕ) (hDN : D ≤ N) :
    (∑ g ∈ Finset.Ioc D N, μ g) = t1_mertensNat N - t1_mertensNat D := by
  have hsub : Finset.Icc 1 D ⊆ Finset.Icc 1 N := by
    intro g hg
    simp only [Finset.mem_Icc] at hg ⊢
    exact ⟨hg.1, hg.2.trans hDN⟩
  have hdiff : Finset.Icc 1 N \ Finset.Icc 1 D = Finset.Ioc D N := by
    ext g
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsum := Finset.sum_sdiff hsub (f := fun g => μ g)
  rw [hdiff] at hsum
  exact eq_sub_iff_add_eq.mpr hsum

/-- Filtering the divisor interval at a point's threshold gives literal
Mertens differences. The min at D handles thresholds below D correctly. -/
theorem t1_mertens_threshold_interval (D N T : ℕ) (hDN : D ≤ N) :
    (∑ g ∈ (Finset.Ioc D N).filter (fun g => g ≤ T), μ g) =
      t1_mertensNat (min N T) - t1_mertensNat (min D T) := by
  have hset : (Finset.Ioc D N).filter (fun g => g ≤ T) =
      Finset.Ioc (min D T) (min N T) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  rw [hset]
  exact t1_mertens_interval _ _ (min_le_min_right T hDN)

/-- Exact finite hyperbola interchange for any finite point set and its
integer thresholds. In applications the thresholds are actual R/length
floors, not an assumed counting correspondence. -/
theorem t1_finite_hyperbola_interchange {α : Type*} (S : Finset α) (T : α → ℕ)
    (D N : ℕ) (hDN : D ≤ N) :
    (∑ g ∈ Finset.Ioc D N, μ g * ((S.filter (fun p => g ≤ T p)).card : ℤ)) =
      ∑ p ∈ S, (t1_mertensNat (min N (T p)) - t1_mertensNat (min D (T p))) := by
  calc
    _ = ∑ g ∈ Finset.Ioc D N, ∑ p ∈ S, if g ≤ T p then μ g else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_comm _ _
    _ = ∑ p ∈ S, ∑ g ∈ Finset.Ioc D N, if g ≤ T p then μ g else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_filter, t1_mertens_threshold_interval D N (T p) hDN]

end Markov
