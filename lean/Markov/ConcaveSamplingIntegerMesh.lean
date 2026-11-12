import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Exact finite-mesh adapters for a function supported in the unit interval. -/

open Set MeasureTheory

namespace Markov

/-- Continuity and vanishing outside the closed unit interval force both endpoint values to vanish. -/
theorem continuous_zero_off_unit_endpoints {f : ℝ → ℝ} (hc : Continuous f)
    (hz : ∀ x, x ∉ Icc (0 : ℝ) 1 → f x = 0) : f 0 = 0 ∧ f 1 = 0 := by
  have hclosed : IsClosed {x : ℝ | f x = 0} := isClosed_eq hc continuous_const
  constructor
  · have hsub : Iio (0 : ℝ) ⊆ {x : ℝ | f x = 0} := by
      intro x hx
      exact hz x (by simp only [mem_Icc, not_and_or]; exact Or.inl (not_le.mpr hx))
    exact (closure_minimal hsub hclosed) (by simp only [closure_Iio, mem_Iic]; exact le_rfl)
  · have hsub : Ioi (1 : ℝ) ⊆ {x : ℝ | f x = 0} := by
      intro x hx
      exact hz x (by simp only [mem_Icc, not_and_or]; exact Or.inr (not_le.mpr hx))
    exact (closure_minimal hsub hclosed) (by simp only [closure_Ioi, mem_Ici]; exact le_rfl)

/-- The global integral is exactly the oriented integral across the unit interval. -/
theorem continuous_zero_off_unit_integral {f : ℝ → ℝ} (hc : Continuous f)
    (hz : ∀ x, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    (∫ x, f x) = ∫ x in (0 : ℝ)..1, f x := by
  apply (intervalIntegral.integral_eq_integral_of_support_subset ?_).symm
  intro x hx
  have hx0 : f x ≠ 0 := hx
  have hmem : x ∈ Icc (0 : ℝ) 1 := by
    by_contra hn
    exact hx0 (hz x hn)
  refine ⟨lt_of_le_of_ne hmem.1 ?_, hmem.2⟩
  intro he
  subst x
  exact hx0 (continuous_zero_off_unit_endpoints hc hz).1

/-- A sampled point lies in the support interval exactly at the indicated integer indices. -/
theorem sampling_mesh_mem_Icc_iff {h : ℝ} (hh : 0 < h) (y : ℝ) (n : ℤ) :
    h * ((n : ℝ) + y) ∈ Icc (0 : ℝ) 1 ↔
      n ∈ Finset.Icc (⌈-y⌉ : ℤ) ⌊1 / h - y⌋ := by
  simp only [mem_Icc, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
  have hone : h * (1 / h) = 1 := mul_one_div_cancel hh.ne'
  constructor
  · rintro ⟨h0, h1⟩
    constructor <;> nlinarith
  · rintro ⟨h0, h1⟩
    constructor <;> nlinarith

/-- Integer samples of a function supported in the unit interval have finite support. -/
theorem sampling_finite_support {f : ℝ → ℝ}
    (hz : ∀ x, x ∉ Icc (0 : ℝ) 1 → f x = 0) {h : ℝ} (hh : 0 < h) (y : ℝ) :
    (Function.support (fun n : ℤ ↦ f (h * ((n : ℝ) + y)))).Finite := by
  apply (Finset.finite_toSet (Finset.Icc (⌈-y⌉ : ℤ) ⌊1 / h - y⌋)).subset
  intro n hn
  apply (sampling_mesh_mem_Icc_iff hh y n).mp
  by_contra hx
  exact hn (hz _ hx)

/-- These integer samples are summable without any further convergence assumption. -/
theorem sampling_summable {f : ℝ → ℝ}
    (hz : ∀ x, x ∉ Icc (0 : ℝ) 1 → f x = 0) {h : ℝ} (hh : 0 < h) (y : ℝ) :
    Summable (fun n : ℤ ↦ f (h * ((n : ℝ) + y))) :=
  summable_of_finite_support (sampling_finite_support hz hh y)

/-- The two-sided integer sum is exactly the sum over the indices hitting the unit interval. -/
theorem sampling_tsum_eq_int_Icc {f : ℝ → ℝ}
    (hz : ∀ x, x ∉ Icc (0 : ℝ) 1 → f x = 0) {h : ℝ} (hh : 0 < h) (y : ℝ) :
    (∑' n : ℤ, f (h * ((n : ℝ) + y))) =
      ∑ n ∈ Finset.Icc (⌈-y⌉ : ℤ) ⌊1 / h - y⌋, f (h * ((n : ℝ) + y)) := by
  apply tsum_eq_sum
  intro n hn
  exact hz _ (fun hx ↦ hn ((sampling_mesh_mem_Icc_iff hh y n).mp hx))

/-- Reindex a finite integer interval by its nonnegative displacement from the left endpoint. -/
theorem sampling_int_Icc_eq_nat_Icc (a b : ℤ) (hab : a ≤ b) (g : ℤ → ℝ) :
    (∑ n ∈ Finset.Icc a b, g n) =
      ∑ j ∈ Finset.Icc 0 (b - a).toNat, g (a + j) := by
  have hcast : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (sub_nonneg.mpr hab)
  symm
  apply Finset.sum_bij (fun (j : ℕ) _ ↦ a + (j : ℤ))
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro i hi j hj hij
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨(n - a).toNat, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro j hj
    rfl

/-- An arbitrary shifted integer lattice is exactly a sufficiently long finite uniform mesh
inside the unit interval. -/
theorem exists_integer_sampling_mesh {f : ℝ → ℝ}
    (hz : ∀ x, x ∉ Icc (0 : ℝ) 1 → f x = 0) {h : ℝ}
    (hh : 0 < h) (hhsmall : h < 1 / 8) (y : ℝ) :
    ∃ (N : ℕ) (u : ℝ), 2 ≤ N ∧ u ∈ Icc 0 h ∧
      u + (N : ℝ) * h ∈ Icc (1 - h) 1 ∧
      (∑' n : ℤ, f (h * ((n : ℝ) + y))) =
        ∑ j ∈ Finset.Icc 0 N, f (u + (j : ℝ) * h) := by
  let a : ℤ := ⌈-y⌉
  let b : ℤ := ⌊1 / h - y⌋
  have ha0 : -y ≤ (a : ℝ) := Int.le_ceil _
  have ha1 : (a : ℝ) < -y + 1 := Int.ceil_lt_add_one _
  have hb0 : (b : ℝ) ≤ 1 / h - y := Int.floor_le _
  have hb1 : 1 / h - y < (b : ℝ) + 1 := Int.lt_floor_add_one _
  have hone : h * (1 / h) = 1 := mul_one_div_cancel hh.ne'
  have hgap : 2 < (b : ℝ) - a := by
    by_contra hn
    have hn' : (b : ℝ) - a ≤ 2 := le_of_not_gt hn
    have hmul := mul_le_mul_of_nonneg_left hn' hh.le
    nlinarith
  have hab : a ≤ b := by
    have hreal : (a : ℝ) ≤ b := by linarith
    exact_mod_cast hreal
  let N : ℕ := (b - a).toNat
  let u : ℝ := h * ((a : ℝ) + y)
  have hNcast : (N : ℤ) = b - a := Int.toNat_of_nonneg (sub_nonneg.mpr hab)
  have hNreal : (N : ℝ) = (b : ℝ) - a := by exact_mod_cast hNcast
  have hN : 2 ≤ N := by
    have hreal : (2 : ℝ) ≤ N := by rw [hNreal]; linarith
    exact_mod_cast hreal
  refine ⟨N, u, hN, ?_, ?_, ?_⟩
  · constructor <;> dsimp [u] <;> nlinarith
  · rw [hNreal]
    constructor <;> dsimp [u] <;> nlinarith
  · rw [sampling_tsum_eq_int_Icc hz hh y]
    change (∑ n ∈ Finset.Icc a b, f (h * ((n : ℝ) + y))) = _
    rw [sampling_int_Icc_eq_nat_Icc a b hab]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    dsimp [u]
    push_cast
    ring

end Markov
