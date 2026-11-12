import T1GeometricPartialCutoff
import T1MoebiusSquareTail

/-! The general primitive-lattice cutoff estimate in the genuine modular
punctured-torus ball. Every geometric ingredient and the exact coefficient
are proved; decay of the actual Mertens envelope remains a separate theorem. -/
noncomputable section
namespace Markov

theorem t1_geometric_primitive_cutoff_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 1 < T ∧
      ∀ R : ℝ, 0 < R → ∀ D : ℕ, 0 < D → T ≤ R / (D + 1) →
        |(t1_geometricPrimitiveCount R : ℝ) -
          (6 * modularMcShaneRivinArea / Real.pi^2) * R^2| ≤
          C * (R * (t1_headLog R (D + 1)) ^ (-(1 : ℝ) / 2) +
            R * (R / D) * t1_mertensEnvelope D) := by
  obtain ⟨C, hC, T, hT, hcut⟩ := t1_geometric_partial_cutoff_bound
  refine ⟨C + 3 * |modularMcShaneRivinArea|,
    add_pos_of_pos_of_nonneg hC (by positivity), T, hT, ?_⟩
  intro R hR D hD hlarge
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hh := hcut R hR D hD hlarge
  have hs := t1_moebiusSquarePartial_tail_bound D hD
  let a := R * (t1_headLog R (D+1)) ^ (-(1 : ℝ)/2)
  let b := R * (R / D) * t1_mertensEnvelope D
  have hlog : 0 < t1_headLog R (D+1) := by
    rw [t1_headLog, ← Real.log_div hR.ne' (by positivity : (D : ℝ)+1 ≠ 0)]
    exact Real.log_pos (hT.trans_le hlarge)
  have ha : 0 ≤ a := mul_nonneg hR.le (Real.rpow_nonneg hlog.le _)
  have hb : 0 ≤ b := by
    dsimp [b]
    exact mul_nonneg (mul_nonneg hR.le (div_nonneg hR.le hDR.le))
      (t1_mertensEnvelope_nonneg D)
  have hcoeff : |modularMcShaneRivinArea * R^2 *
      (t1_moebiusSquarePartial D - 6 / Real.pi^2)| ≤
      3 * |modularMcShaneRivinArea| * b := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg R)]
    calc
      _ ≤ |modularMcShaneRivinArea| * R^2 *
          (3 * t1_mertensEnvelope D / D) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by dsimp [b]; ring
  have hid : (t1_geometricPrimitiveCount R : ℝ) -
      (6 * modularMcShaneRivinArea / Real.pi^2) * R^2 =
      ((t1_geometricPrimitiveCount R : ℝ) -
        modularMcShaneRivinArea * R^2 * t1_moebiusSquarePartial D) +
      modularMcShaneRivinArea * R^2 *
        (t1_moebiusSquarePartial D - 6 / Real.pi^2) := by ring
  rw [hid]
  calc
    _ ≤ |(t1_geometricPrimitiveCount R : ℝ) -
        modularMcShaneRivinArea * R^2 * t1_moebiusSquarePartial D| +
        |modularMcShaneRivinArea * R^2 *
          (t1_moebiusSquarePartial D - 6 / Real.pi^2)| := abs_add_le _ _
    _ ≤ C * (a+b) + 3 * |modularMcShaneRivinArea| * b :=
      add_le_add hh hcoeff
    _ ≤ _ := by
      change _ ≤ (C + 3 * |modularMcShaneRivinArea|) * (a+b)
      nlinarith [mul_nonneg (abs_nonneg modularMcShaneRivinArea) ha]

end Markov
