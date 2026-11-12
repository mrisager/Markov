import T1LogarithmicHeadSum
import T1UniformLatticeError

/-! The small-divisor error for the actual geometric nonzero count.
The uniform lattice error is derived from the already proved Theorem 12. -/

noncomputable section
open Classical Finset Set
open scoped ArithmeticFunction.Moebius
namespace Markov

theorem t1_headWeight_eq_kernel (R x : ℝ) (hR : 0 < R) (hx : 0 < x)
    (hlog : 0 < t1_headLog R x) :
    t1_headWeight R x = 1 / (x * Real.log (R / x) ^ ((3 : ℝ) / 2)) := by
  have hpow : (t1_headLog R x) ^ (-(3 : ℝ) / 2) =
      ((t1_headLog R x) ^ ((3 : ℝ) / 2))⁻¹ := by
    simpa only [neg_div] using Real.rpow_neg hlog.le ((3 : ℝ) / 2)
  rw [t1_headWeight, hpow, t1_headLog, ← Real.log_div hR.ne' hx.ne']
  simp only [one_div, mul_inv_rev]
  ring

theorem t1_errorScale_at_div (R x : ℝ) (hR : 0 < R) (hx : 0 < x)
    (hlog : 0 < t1_headLog R x) :
    t1_latticeErrorScale (R / x) = R * t1_headWeight R x := by
  rw [t1_headWeight_eq_kernel R x hR hx hlog, t1_latticeErrorScale]
  simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
  ring

def t1_geometricMobiusHead (R : ℝ) (D : ℕ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 D,
    (μ g : ℝ) * ((modularMcShaneRivinLatticeCount (R / g) - 1 : ℕ) : ℝ)

def t1_moebiusSquarePartial (D : ℕ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 D, (μ g : ℝ) / (g : ℝ) ^ 2

theorem t1_geometric_head_error_identity (R : ℝ) (D : ℕ) :
    t1_geometricMobiusHead R D - modularMcShaneRivinArea * R ^ 2 * t1_moebiusSquarePartial D =
      ∑ g ∈ Finset.Icc 1 D, (μ g : ℝ) * t1_nonzeroLatticeError (R / g) := by
  rw [t1_geometricMobiusHead, t1_moebiusSquarePartial, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro g _
  simp only [t1_nonzeroLatticeError, div_eq_mul_inv]
  ring

/-- A proved uniform small-divisor estimate for the genuine geometric
count. The square-root-log endpoint R/(D+1) is explicit, and the constants
and large-radius threshold come from the completed Theorem 12. -/
theorem t1_geometric_small_divisor_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 1 < T ∧
      ∀ R : ℝ, 0 < R → ∀ D : ℕ, T ≤ R / (D + 1) →
        |t1_geometricMobiusHead R D -
          modularMcShaneRivinArea * R ^ 2 * t1_moebiusSquarePartial D| ≤
          C * R * (t1_headLog R (D + 1)) ^ (-(1 : ℝ) / 2) := by
  obtain ⟨C, hC, T, hT, herror⟩ := t1_uniform_nonzero_lattice_error
  refine ⟨4 * C, by positivity, T, hT, ?_⟩
  intro R hR D hcut
  have hb : (0 : ℝ) < D + 1 := by positivity
  have hlog : 0 < t1_headLog R (D + 1) := by
    rw [t1_headLog, ← Real.log_div hR.ne' hb.ne']
    exact Real.log_pos (hT.trans_le hcut)
  have hpoint (g : ℕ) (hg : g ∈ Finset.Icc 1 D) :
      |(μ g : ℝ) * t1_nonzeroLatticeError (R / g)| ≤ C * R * t1_headWeight R g := by
    obtain ⟨hg1, hgD⟩ := Finset.mem_Icc.mp hg
    have hgpos : (0 : ℝ) < g := by exact_mod_cast hg1
    have hgb : (g : ℝ) ≤ D + 1 := by exact_mod_cast Nat.le_succ_of_le hgD
    have hcompare : R / (D + 1) ≤ R / g :=
      (div_le_div_iff₀ hb hgpos).mpr (mul_le_mul_of_nonneg_left hgb hR.le)
    have hlarge := hcut.trans hcompare
    have hlogg := t1_headLog_pos_on R (D + 1) hlog
      (show (g : ℝ) ∈ Set.Icc 1 (D + 1 : ℝ) from
        ⟨by exact_mod_cast hg1, hgb⟩)
    have hmu : |(μ g : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := g)
    calc
      _ = |(μ g : ℝ)| * |t1_nonzeroLatticeError (R / g)| := abs_mul _ _
      _ ≤ 1 * |t1_nonzeroLatticeError (R / g)| :=
        mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
      _ ≤ C * t1_latticeErrorScale (R / g) := by simpa only [one_mul] using herror _ hlarge
      _ = _ := by rw [t1_errorScale_at_div R g hR hgpos hlogg]; ring
  rw [t1_geometric_head_error_identity]
  calc
    _ ≤ ∑ g ∈ Finset.Icc 1 D, |(μ g : ℝ) * t1_nonzeroLatticeError (R / g)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ g ∈ Finset.Icc 1 D, C * R * t1_headWeight R g := Finset.sum_le_sum hpoint
    _ = C * R * (∑ g ∈ Finset.Icc 1 D, t1_headWeight R g) := (Finset.mul_sum _ _ _).symm
    _ ≤ C * R * (4 * (t1_headLog R (D + 1)) ^ (-(1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left (t1_logarithmic_head_weight_sum R D hlog)
        (mul_nonneg hC.le hR.le)
    _ = _ := by ring

end Markov
