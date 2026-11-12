import Markov.PaperQuadrilateralInversion

/-! Exact coverage of the upper part of the actual paper quadrilateral by
five signed half-cell pieces. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- The central sign in `S² = -I` acts trivially on the upper half-plane. -/
theorem modular_S_smul_involutive (z : UpperHalfPlane) :
    ModularGroup.S • (ModularGroup.S • z) = z := by
  rw [← mul_smul, ← pow_two, modularIntegral_S_pow_two,
    ModularGroup.SL_neg_smul, one_smul]

/-- Exact upper-quadrilateral coverage, retaining literal word order and
all half-cell coordinate conditions. -/
theorem paperIdealQuadrilateral_upper_coverage (z : UpperHalfPlane)
    (hQ : z ∈ paperIdealQuadrilateral) (hN : 1 ≤ Complex.normSq (z : ℂ)) :
    ∃ w ∈ ModularGroup.fd,
      z = w ∨
      (w.re ≤ 0 ∧ z = ModularGroup.T • w) ∨
      (0 ≤ w.re ∧ z = ModularGroup.T⁻¹ • w) ∨
      (0 ≤ w.re ∧ z = (ModularGroup.T * ModularGroup.S) • w) ∨
      (w.re ≤ 0 ∧ z = (ModularGroup.T⁻¹ * ModularGroup.S) • w) := by
  have hx := abs_le.mp ((paperIdealQuadrilateral_mem_iff_abs_re z).mp hQ).1
  by_cases hl : z.re < -1 / 2
  · let v := ModularGroup.T • z
    have hvr : v.re = z.re + 1 := ModularGroup.re_T_smul z
    have hvN : Complex.normSq (v : ℂ) = Complex.normSq (z : ℂ) + 2 * z.re + 1 :=
      modular_normSq_T_smul z
    by_cases hv : 1 ≤ Complex.normSq (v : ℂ)
    · have hvfd : v ∈ ModularGroup.fd :=
        ⟨hv, abs_le.mpr ⟨by linarith [hx.1], by linarith⟩⟩
      refine ⟨v, hvfd, Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))⟩
      · linarith [hx.1]
      · dsimp only [v]
        rw [inv_smul_smul]
    · let w := ModularGroup.S • v
      have hwN : 1 ≤ Complex.normSq (w : ℂ) := by
        dsimp only [w]
        rw [modular_normSq_S_smul]
        rw [← one_div]
        apply (le_div_iff₀ v.normSq_pos).mpr
        simpa only [one_mul] using (le_of_not_ge hv)
      have hwr : w.re = -(z.re + 1) / Complex.normSq (v : ℂ) := by
        dsimp only [w]
        rw [modular_S_re_div_normSq, hvr]
      have hwrneg : w.re ≤ 0 := by
        rw [hwr]
        exact div_nonpos_of_nonpos_of_nonneg (by linarith [hx.1]) v.normSq_pos.le
      have hwrlo : -1 / 2 ≤ w.re := by
        rw [hwr, le_div_iff₀ v.normSq_pos, hvN]
        nlinarith
      have hwfd : w ∈ ModularGroup.fd :=
        ⟨hwN, abs_le.mpr ⟨by linarith [hwrlo], by linarith⟩⟩
      refine ⟨w, hwfd, Or.inr (Or.inr (Or.inr (Or.inr ⟨hwrneg, ?_⟩)))⟩
      dsimp only [w, v]
      rw [mul_smul, modular_S_smul_involutive, inv_smul_smul]
  · by_cases hr : 1 / 2 < z.re
    · let v := ModularGroup.T⁻¹ • z
      have hvr : v.re = z.re - 1 := ModularGroup.re_T_inv_smul z
      have hvN : Complex.normSq (v : ℂ) = Complex.normSq (z : ℂ) - 2 * z.re + 1 :=
        modular_normSq_T_inv_smul z
      by_cases hv : 1 ≤ Complex.normSq (v : ℂ)
      · have hvfd : v ∈ ModularGroup.fd :=
          ⟨hv, abs_le.mpr ⟨by linarith, by linarith [hx.2]⟩⟩
        refine ⟨v, hvfd, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
        · linarith [hx.2]
        · dsimp only [v]
          rw [smul_inv_smul]
      · let w := ModularGroup.S • v
        have hwN : 1 ≤ Complex.normSq (w : ℂ) := by
          dsimp only [w]
          rw [modular_normSq_S_smul]
          rw [← one_div]
          apply (le_div_iff₀ v.normSq_pos).mpr
          simpa only [one_mul] using (le_of_not_ge hv)
        have hwr : w.re = (1 - z.re) / Complex.normSq (v : ℂ) := by
          dsimp only [w]
          rw [modular_S_re_div_normSq, hvr]
          congr 1
          ring
        have hwrpos : 0 ≤ w.re := by
          rw [hwr]
          exact div_nonneg (by linarith [hx.2]) v.normSq_pos.le
        have hwrhi : w.re ≤ 1 / 2 := by
          rw [hwr, div_le_iff₀ v.normSq_pos, hvN]
          nlinarith
        have hwfd : w ∈ ModularGroup.fd :=
          ⟨hwN, abs_le.mpr ⟨by linarith, hwrhi⟩⟩
        refine ⟨w, hwfd, Or.inr (Or.inr (Or.inr (Or.inl ⟨hwrpos, ?_⟩)))⟩
        dsimp only [w, v]
        rw [mul_smul, modular_S_smul_involutive, smul_inv_smul]
    · exact ⟨z, ⟨hN, abs_le.mpr ⟨by linarith, by linarith⟩⟩, Or.inl rfl⟩

end Markov
