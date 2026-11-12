import Markov.TraceAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! A quantitative upper bound on the deficit between a positive-root
length and the logarithmic value of an inward supporting functional.
Only real algebraic coefficient data are used here. -/

noncomputable section
namespace Markov

/-- On the upper Fricke branch, the inward coefficient differs from the
expanding root by a uniformly small logarithmic deficit. -/
theorem logarithmic_coefficient_deficit_bounds
    (t b A A' s : ℝ) (ht : 3 ≤ t) (hb : 3 ≤ b)
    (hA : 0 < A) (hs : 1 < s)
    (hsum : A + A' = b) (hprod : A * A' = t ^ 2 / (t ^ 2 - 4))
    (hlarge : b / 2 ≤ A) (hroot : s + s⁻¹ = b) :
    0 ≤ 2 * Real.log s - 2 * Real.log A ∧
      2 * Real.log s - 2 * Real.log A ≤ 96 / (t ^ 2 * b ^ 2) := by
  have ht0 : 0 < t := by linarith
  have hb0 : 0 < b := by linarith
  have hs0 : 0 < s := by linarith
  have hd : 0 < t ^ 2 - 4 := by nlinarith
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht0
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb0
  have hunit : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
  have hseq : s ^ 2 + 1 = b * s := by
    calc
      s ^ 2 + 1 = s * (s + s⁻¹) := by nlinarith [hunit]
      _ = b * s := by rw [hroot]; ring
  have hstwo : 2 ≤ s := by
    by_contra hn
    have hslt : s < 2 := lt_of_not_ge hn
    have hsquare : s ^ 2 < 2 * s := by
      nlinarith [mul_lt_mul_of_pos_right hslt hs0]
    nlinarith
  have hinv : s⁻¹ ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_right hstwo (inv_nonneg.mpr hs0.le)
    rw [hunit] at hh
    linarith
  have hfac : b / 3 ≤ A - s⁻¹ := by linarith
  have hfacpos : 0 < A - s⁻¹ := lt_of_lt_of_le (by positivity) hfac
  have hprodsub : A * A' - 1 = 4 / (t ^ 2 - 4) := by
    rw [hprod]
    field_simp
    ring
  have hidentity : (s - A) * (A - s⁻¹) = 4 / (t ^ 2 - 4) := by
    calc
      (s - A) * (A - s⁻¹) = A * (s + s⁻¹) - A ^ 2 - s * s⁻¹ := by ring
      _ = A * (A + A') - A ^ 2 - 1 := by rw [hroot, ← hsum, hunit]
      _ = A * A' - 1 := by ring
      _ = _ := hprodsub
  have hgap : 0 ≤ s - A := by
    have hh : 0 < (s - A) * (A - s⁻¹) := by rw [hidentity]; positivity
    exact (pos_of_mul_pos_left hh hfacpos.le).le
  have hgapbound : s - A ≤ 3 * (4 / (t ^ 2 - 4)) / b := by
    apply (le_div_iff₀ hb0).mpr
    have hh := mul_le_mul_of_nonneg_left hfac hgap
    rw [hidentity] at hh
    nlinarith
  have hratio : (s - A) / A ≤ 6 * (4 / (t ^ 2 - 4)) / b ^ 2 := by
    calc
      (s - A) / A ≤ (3 * (4 / (t ^ 2 - 4)) / b) / A :=
        div_le_div_of_nonneg_right hgapbound hA.le
      _ ≤ (3 * (4 / (t ^ 2 - 4)) / b) / (b / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlarge
      _ = _ := by field_simp; ring
  have hD : 4 / (t ^ 2 - 4) ≤ 8 / t ^ 2 := by
    apply (div_le_div_iff₀ hd ht2).mpr
    nlinarith
  have hlog : Real.log s - Real.log A ≤ (s - A) / A := by
    rw [← Real.log_div hs0.ne' hA.ne']
    have hh := Real.log_le_sub_one_of_pos (div_pos hs0 hA)
    have he : s / A - 1 = (s - A) / A := by field_simp
    rwa [he] at hh
  refine ⟨by linarith [Real.log_le_log hA (by linarith : A ≤ s)], ?_⟩
  calc
    2 * Real.log s - 2 * Real.log A ≤ 2 * ((s - A) / A) := by linarith
    _ ≤ 12 * (4 / (t ^ 2 - 4)) / b ^ 2 := by
      convert mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2) using 1
      ring
    _ ≤ 12 * (8 / t ^ 2) / b ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hD (by norm_num)) hb2.le
    _ = 96 / (t ^ 2 * b ^ 2) := by field_simp; ring

end Markov
