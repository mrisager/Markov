import T1MertensSquareAbel

/-! A genuine uniform bound for finite Möbius square-series tails, obtained
by discrete partial summation and the actual Mertens supremum. -/
noncomputable section
open Classical Finset
open scoped ArithmeticFunction.Moebius
namespace Markov

theorem t1_mertens_square_kernel_sum_bound (D N : ℕ) (hD : 0 < D) (hDN : D ≤ N) :
    (∑ g ∈ Finset.Ico D N, |(t1_mertensNat g : ℝ)| *
      (1 / (g : ℝ)^2 - 1 / ((g : ℝ)+1)^2)) ≤
      2 * t1_mertensEnvelope D * (1 / (D : ℝ) - 1 / (N : ℝ)) := by
  calc
    _ ≤ ∑ g ∈ Finset.Ico D N, t1_mertensEnvelope D *
        (2 * (1 / (g : ℝ) - 1 / ((g : ℝ)+1))) := by
      apply Finset.sum_le_sum
      intro g hg
      have hDg := (Finset.mem_Ico.mp hg).1
      have hgR : (0 : ℝ) < g := by exact_mod_cast hD.trans_le hDg
      calc
        _ ≤ (t1_mertensEnvelope D * g) *
            (1 / (g : ℝ)^2 - 1 / ((g : ℝ)+1)^2) :=
          mul_le_mul_of_nonneg_right (t1_mertensEnvelope_dominates D g hDg)
            (t1_square_abel_kernel_nonneg _ hgR)
        _ = t1_mertensEnvelope D * ((g : ℝ) *
            (1 / (g : ℝ)^2 - 1 / ((g : ℝ)+1)^2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (t1_square_abel_kernel_bound _ hgR)
          (t1_mertensEnvelope_nonneg D)
    _ = _ := by
      rw [← Finset.mul_sum]
      rw [← Finset.mul_sum, t1_reciprocal_interval_telescope D N hDN]
      ring

theorem t1_moebius_square_finite_tail_bound (D N : ℕ) (hD : 0 < D) (hDN : D ≤ N) :
    |∑ g ∈ Finset.Ioc D N, (μ g : ℝ) / (g : ℝ)^2| ≤
      3 * t1_mertensEnvelope D / D := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hNR : (0 : ℝ) < N := by exact_mod_cast hD.trans_le hDN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNR
  have hD0 : (D : ℝ) ≠ 0 := ne_of_gt hDR
  have hbdN : |(t1_mertensNat N : ℝ) / (N : ℝ)^2| ≤
      t1_mertensEnvelope D / N := by
    rw [abs_div, abs_of_nonneg (sq_nonneg (N : ℝ))]
    calc
      _ ≤ (t1_mertensEnvelope D * N) / (N : ℝ)^2 :=
        div_le_div_of_nonneg_right (t1_mertensEnvelope_dominates D N hDN) (sq_nonneg _)
      _ = _ := by field_simp
  have hbdD : |(t1_mertensNat D : ℝ) / (D : ℝ)^2| ≤
      t1_mertensEnvelope D / D := by
    rw [abs_div, abs_of_nonneg (sq_nonneg (D : ℝ))]
    calc
      _ ≤ (t1_mertensEnvelope D * D) / (D : ℝ)^2 :=
        div_le_div_of_nonneg_right (t1_mertensEnvelope_dominates D D le_rfl) (sq_nonneg _)
      _ = _ := by field_simp
  have hsum : |∑ g ∈ Finset.Ico D N, (t1_mertensNat g : ℝ) *
      (1 / (g : ℝ)^2 - 1 / ((g : ℝ)+1)^2)| ≤
      2 * t1_mertensEnvelope D * (1 / (D : ℝ) - 1 / (N : ℝ)) := by
    calc
      _ ≤ ∑ g ∈ Finset.Ico D N, |(t1_mertensNat g : ℝ)| *
          (1 / (g : ℝ)^2 - 1 / ((g : ℝ)+1)^2) := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro g hg
        have hgR : (0 : ℝ) < g := by
          exact_mod_cast hD.trans_le (Finset.mem_Ico.mp hg).1
        rw [abs_mul, abs_of_nonneg (t1_square_abel_kernel_nonneg _ hgR)]
      _ ≤ _ := t1_mertens_square_kernel_sum_bound D N hD hDN
  rw [t1_moebius_square_abel D N hDN]
  calc
    _ ≤ |(t1_mertensNat N : ℝ) / (N : ℝ)^2| +
        |(t1_mertensNat D : ℝ) / (D : ℝ)^2| +
        |∑ g ∈ Finset.Ico D N, (t1_mertensNat g : ℝ) *
          (1 / (g : ℝ)^2 - 1 / ((g : ℝ)+1)^2)| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ t1_mertensEnvelope D / N + t1_mertensEnvelope D / D +
        2 * t1_mertensEnvelope D * (1 / (D : ℝ) - 1 / (N : ℝ)) :=
      add_le_add (add_le_add hbdN hbdD) hsum
    _ ≤ _ := by
      have hnon : 0 ≤ t1_mertensEnvelope D / N :=
        div_nonneg (t1_mertensEnvelope_nonneg D) hNR.le
      simp only [div_eq_mul_inv] at *
      nlinarith

end Markov
