import Markov.SupportCoordinates
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod

/-! The elementary counting and denominator estimates of v1 Lemma 3. -/

noncomputable section
namespace Markov

/-- All primitive integral directions in the actual height cutoff square. -/
def primitiveDirectionsUpTo (H : ℕ) : Finset (ℤ × ℤ) := by
  classical
  exact ((Finset.Icc (-(H : ℤ)) H).product (Finset.Icc (-(H : ℤ)) H)).filter
    (fun p => IsCoprime p.1 p.2)

theorem mem_primitiveDirectionsUpTo (H : ℕ) (p : ℤ × ℤ) :
    p ∈ primitiveDirectionsUpTo H ↔ IsCoprime p.1 p.2 ∧ intHeight p ≤ H := by
  classical
  simp only [primitiveDirectionsUpTo, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_Icc, intHeight, max_le_iff, abs_le]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩, hp⟩
    exact ⟨hp, ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩,
      ⟨by exact_mod_cast h2, by exact_mod_cast h3⟩⟩
  · rintro ⟨hp, ⟨h0, h1⟩, ⟨h2, h3⟩⟩
    exact ⟨⟨⟨by exact_mod_cast h0, by exact_mod_cast h1⟩,
      ⟨by exact_mod_cast h2, by exact_mod_cast h3⟩⟩, hp⟩

theorem primitiveDirectionsUpTo_card_le (H : ℕ) :
    (primitiveDirectionsUpTo H).card ≤ (2 * H + 1) ^ 2 := by
  classical
  have h : (Finset.Icc (-(H : ℤ)) H).card = 2 * H + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    (primitiveDirectionsUpTo H).card ≤
        ((Finset.Icc (-(H : ℤ)) H).product (Finset.Icc (-(H : ℤ)) H)).card :=
      Finset.card_filter_le _ _
    _ = (2 * H + 1) ^ 2 := by rw [Finset.product_eq_sprod, Finset.card_product, h]; ring

/-- Exact slope spacing from the determinant-one condition. -/
theorem farey_slope_gap (p q r s : ℝ) (hp : 0 < p) (hr : 0 < r)
    (hdet : |p * s - q * r| = 1) :
    |q / p - s / r| = 1 / (p * r) := by
  have he : q / p - s / r = -(p * s - q * r) / (p * r) := by
    field_simp
    ring
  rw [he, abs_div, abs_neg, hdet, abs_of_pos (mul_pos hp hr)]

/-- The denominator step used after consecutive cutoff Farey fractions
have been identified. No cutoff-neighbor theorem is assumed implicitly. -/
theorem farey_reciprocal_scale (p r H : ℝ) (hp : 0 < p) (hr : 0 < r)
    (hH : 0 < H) (hcutoff : H < p + r) :
    1 / (p * r) ≤ 2 / (H * min p r) := by
  have hm : 0 < min p r := lt_min hp hr
  apply (div_le_div_iff₀ (mul_pos hp hr) (mul_pos hH hm)).mpr
  rcases le_total p r with h | h
  · rw [min_eq_left h]
    have hle : H ≤ 2 * r := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hle hp.le]
  · rw [min_eq_right h]
    have hle : H ≤ 2 * p := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hle hr.le]

theorem farey_slope_gap_le_scale (p q r s H : ℝ) (hp : 0 < p) (hr : 0 < r)
    (hH : 0 < H) (hcutoff : H < p + r) (hdet : |p * s - q * r| = 1) :
    |q / p - s / r| ≤ 2 / (H * min p r) := by
  rw [farey_slope_gap p q r s hp hr hdet]
  exact farey_reciprocal_scale p r H hp hr hH hcutoff

end Markov
