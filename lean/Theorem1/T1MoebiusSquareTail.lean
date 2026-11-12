import T1MertensSquareFiniteBound
import T1MoebiusSquareCoefficient
import T1SmallDivisorHead

/-! Passage from genuine finite Abel bounds to the actual infinite Möbius
square-series tail. No decay premise is needed for this cutoff estimate. -/
noncomputable section
open Classical Finset Filter
open scoped ArithmeticFunction.Moebius Topology
namespace Markov

theorem t1_moebiusSquarePartial_eq_range (N : ℕ) :
    t1_moebiusSquarePartial N = ∑ g ∈ Finset.range (N+1), t1_moebiusSquareTerm g := by
  have hs : Finset.range (N+1) = insert 0 (Finset.Icc 1 N) := by
    ext g
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hs, Finset.sum_insert (by simp)]
  simp [t1_moebiusSquareTerm, t1_moebiusSquarePartial]

theorem t1_moebiusSquarePartial_tendsto :
    Tendsto t1_moebiusSquarePartial atTop (𝓝 (6 / Real.pi^2)) := by
  have h := t1_moebiusSquareTerm_summable.hasSum.tendsto_sum_nat
  rw [t1_moebiusSquareTerm_tsum] at h
  simpa only [Function.comp_def, ← t1_moebiusSquarePartial_eq_range] using
    h.comp (tendsto_add_atTop_nat 1)

theorem t1_moebiusSquarePartial_interval (D N : ℕ) (hDN : D ≤ N) :
    t1_moebiusSquarePartial N - t1_moebiusSquarePartial D =
      ∑ g ∈ Finset.Ioc D N, (μ g : ℝ) / (g : ℝ)^2 := by
  have hsub : Finset.Icc 1 D ⊆ Finset.Icc 1 N := by
    intro g hg
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hg).1,
      (Finset.mem_Icc.mp hg).2.trans hDN⟩
  have hdiff : Finset.Icc 1 N \ Finset.Icc 1 D = Finset.Ioc D N := by
    ext g
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsum := Finset.sum_sdiff hsub (f := fun g => (μ g : ℝ) / (g : ℝ)^2)
  rw [hdiff] at hsum
  exact eq_sub_iff_add_eq.mpr hsum |>.symm

theorem t1_moebiusSquarePartial_tail_bound (D : ℕ) (hD : 0 < D) :
    |t1_moebiusSquarePartial D - 6 / Real.pi^2| ≤
      3 * t1_mertensEnvelope D / D := by
  have hlim := (t1_moebiusSquarePartial_tendsto.sub_const
    (t1_moebiusSquarePartial D)).abs
  have hev : ∀ᶠ N : ℕ in atTop,
      |t1_moebiusSquarePartial N - t1_moebiusSquarePartial D| ≤
        3 * t1_mertensEnvelope D / D := by
    filter_upwards [eventually_ge_atTop D] with N hN
    rw [t1_moebiusSquarePartial_interval D N hN]
    exact t1_moebius_square_finite_tail_bound D N hD hN
  have hb := le_of_tendsto hlim hev
  rwa [abs_sub_comm] at hb

end Markov
