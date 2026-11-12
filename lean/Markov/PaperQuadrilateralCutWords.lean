import Markov.PaperQuadrilateralInversion
import Markov.ModularSixCellBoundary

/-! Actual half-cell representatives in the literal paper quadrilateral,
with their exact projective cyclic labels. No piecewise continuity is asserted. -/
noncomputable section
open scoped MatrixGroups
namespace Markov

theorem paperIdealQuadrilateral_mem_of_fd (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) : z ∈ paperIdealQuadrilateral := by
  apply (paperIdealQuadrilateral_mem_iff_abs_re z).mpr
  constructor <;> linarith [hz.1, hz.2]

theorem paperIdealQuadrilateral_T_mem_of_fd_left (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) (hleft : z.re ≤ 0) :
    ModularGroup.T • z ∈ paperIdealQuadrilateral := by
  apply (paperIdealQuadrilateral_mem_iff_abs_re _).mpr
  rw [ModularGroup.re_T_smul]
  have hx := abs_le.mp hz.2
  rw [abs_of_nonneg (by linarith : 0 ≤ z.re + 1)]
  constructor
  · linarith
  · rw [modular_normSq_T_smul]
    linarith [hz.1]

theorem paperIdealQuadrilateral_T_inv_mem_of_fd_right (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) (hright : 0 ≤ z.re) :
    ModularGroup.T⁻¹ • z ∈ paperIdealQuadrilateral := by
  apply (paperIdealQuadrilateral_mem_iff_abs_re _).mpr
  rw [ModularGroup.re_T_inv_smul]
  have hx := abs_le.mp hz.2
  rw [abs_of_nonpos (by linarith : z.re - 1 ≤ 0)]
  constructor
  · linarith
  · rw [modular_normSq_T_inv_smul]
    linarith [hz.1]

theorem paperIdealQuadrilateral_TS_mem_of_fd_right (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) (hright : 0 ≤ z.re) :
    (ModularGroup.T * ModularGroup.S) • z ∈ paperIdealQuadrilateral := by
  rw [mul_smul]
  apply (paperIdealQuadrilateral_mem_iff_abs_re _).mpr
  rw [ModularGroup.re_T_smul, modular_S_re_div_normSq]
  have hN := z.normSq_pos
  have hx := abs_le.mp hz.2
  have h0 : 0 ≤ z.re / Complex.normSq (z : ℂ) := div_nonneg hright hN.le
  have hhalf : z.re / Complex.normSq (z : ℂ) ≤ 1 / 2 :=
    (div_le_iff₀ hN).mpr (by nlinarith [hz.1])
  have hfrac : z.re / Complex.normSq (z : ℂ) ≤ (Complex.normSq (z : ℂ))⁻¹ := by
    rw [inv_eq_one_div]
    exact (div_le_div_iff_of_pos_right hN).mpr (by linarith)
  rw [neg_div, abs_of_nonneg (by linarith : 0 ≤ -(z.re / Complex.normSq (z : ℂ)) + 1)]
  constructor
  · linarith
  · rw [modular_normSq_T_smul, modular_normSq_S_smul, modular_S_re_div_normSq,
      neg_div]
    linarith

theorem paperIdealQuadrilateral_T_inv_S_mem_of_fd_left (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) (hleft : z.re ≤ 0) :
    (ModularGroup.T⁻¹ * ModularGroup.S) • z ∈ paperIdealQuadrilateral := by
  rw [mul_smul]
  apply (paperIdealQuadrilateral_mem_iff_abs_re _).mpr
  rw [ModularGroup.re_T_inv_smul, modular_S_re_div_normSq]
  have hN := z.normSq_pos
  have hx := abs_le.mp hz.2
  have h0 : z.re / Complex.normSq (z : ℂ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hleft hN.le
  have hhalf : -(1 / 2 : ℝ) ≤ z.re / Complex.normSq (z : ℂ) :=
    (le_div_iff₀ hN).mpr (by nlinarith [hz.1])
  have hfrac : -(Complex.normSq (z : ℂ))⁻¹ ≤ z.re / Complex.normSq (z : ℂ) := by
    rw [inv_eq_one_div, ← neg_div]
    exact (div_le_div_iff_of_pos_right hN).mpr (by linarith)
  rw [neg_div, abs_of_nonpos (by linarith : -(z.re / Complex.normSq (z : ℂ)) - 1 ≤ 0)]
  constructor
  · linarith
  · rw [modular_normSq_T_inv_smul, modular_normSq_S_smul, modular_S_re_div_normSq,
      neg_div]
    linarith

/-- Left/right half-cell representatives, indexed by the actual cyclic residue.
The split is a selection of representatives, without a continuity assertion. -/
def paperQuadrilateralCutWord (r : Fin 6) (left : Bool) : SL(2, ℤ) :=
  if left then
    ![1, ModularGroup.T, ModularGroup.T⁻¹ * ModularGroup.S, ModularGroup.S,
      ModularGroup.S * ModularGroup.T, ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.S] r
  else
    ![1, ModularGroup.S * ModularGroup.T * ModularGroup.S, ModularGroup.S * ModularGroup.T⁻¹,
      ModularGroup.S, ModularGroup.T * ModularGroup.S, ModularGroup.T⁻¹] r

/-- Each selected literal half-cell word lands in the actual quadrilateral. -/
theorem paperQuadrilateralCutWord_mem (r : Fin 6) (left : Bool) (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd)
    (hside : if left then z.re ≤ 0 else 0 ≤ z.re) :
    paperQuadrilateralCutWord r left • z ∈ paperIdealQuadrilateral := by
  cases left
  · simp only [Bool.false_eq_true, ↓reduceIte] at hside
    fin_cases r <;> simp only [paperQuadrilateralCutWord, Bool.false_eq_true, ↓reduceIte,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk]
    · simpa only [one_smul] using paperIdealQuadrilateral_mem_of_fd z hz
    · rw [mul_smul, mul_smul, paperIdealQuadrilateral_S_mem_iff]
      simpa only [mul_smul] using paperIdealQuadrilateral_TS_mem_of_fd_right z hz hside
    · rw [mul_smul, paperIdealQuadrilateral_S_mem_iff]
      exact paperIdealQuadrilateral_T_inv_mem_of_fd_right z hz hside
    · exact (paperIdealQuadrilateral_S_mem_iff z).mpr (paperIdealQuadrilateral_mem_of_fd z hz)
    · exact paperIdealQuadrilateral_TS_mem_of_fd_right z hz hside
    · exact paperIdealQuadrilateral_T_inv_mem_of_fd_right z hz hside
  · simp only [↓reduceIte] at hside
    fin_cases r <;> simp only [paperQuadrilateralCutWord, ↓reduceIte,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk]
    · simpa only [one_smul] using paperIdealQuadrilateral_mem_of_fd z hz
    · exact paperIdealQuadrilateral_T_mem_of_fd_left z hz hside
    · exact paperIdealQuadrilateral_T_inv_S_mem_of_fd_left z hz hside
    · exact (paperIdealQuadrilateral_S_mem_iff z).mpr (paperIdealQuadrilateral_mem_of_fd z hz)
    · rw [mul_smul, paperIdealQuadrilateral_S_mem_iff]
      exact paperIdealQuadrilateral_T_mem_of_fd_left z hz hside
    · rw [mul_smul, mul_smul, paperIdealQuadrilateral_S_mem_iff]
      simpa only [mul_smul] using paperIdealQuadrilateral_T_inv_S_mem_of_fd_left z hz hside

set_option maxHeartbeats 800000 in
/-- Every selected half-cell word has the residue of its source cell. -/
theorem paperQuadrilateralCutWord_quotient (r : Fin 6) (left : Bool) :
    modularTraceProjectiveQuotientMap (paperQuadrilateralCutWord r left) =
      modularTraceProjectiveQuotientT ^ r.val := by
  generalize ht : modularTraceProjectiveQuotientT = t
  have hS : modularTraceProjectiveQuotientMap ModularGroup.S = t ^ 3 := by
    rw [← ht]
    exact modularTraceProjectiveQuotientS_eq_T_pow_three
  have hT : modularTraceProjectiveQuotientMap ModularGroup.T = t := ht
  have hinv : t⁻¹ = t ^ 5 := by
    rw [← ht]
    exact modularTraceProjectiveQuotientT_inv_eq_pow_five
  have hord : orderOf t = 6 := by
    rw [← ht]
    exact modularTraceProjectiveQuotientT_orderOf
  have hmod (n : ℕ) : t ^ n = t ^ (n % 6) := by
    simpa only [hord] using (pow_mod_orderOf t n).symm
  cases left
  · fin_cases r
    · change modularTraceProjectiveQuotientMap 1 = t ^ 0
      simp only [map_one, pow_zero]
    · change modularTraceProjectiveQuotientMap
        (ModularGroup.S * ModularGroup.T * ModularGroup.S) = t ^ 1
      rw [map_mul, map_mul, hS, hT]
      calc
        t ^ 3 * t * t ^ 3 = t ^ 7 := by group
        _ = t ^ 1 := by rw [hmod 7]
    · change modularTraceProjectiveQuotientMap
        (ModularGroup.S * ModularGroup.T⁻¹) = t ^ 2
      rw [map_mul, map_inv, hS, hT, hinv, ← pow_add, hmod 8]
    · change modularTraceProjectiveQuotientMap ModularGroup.S = t ^ 3
      exact hS
    · change modularTraceProjectiveQuotientMap
        (ModularGroup.T * ModularGroup.S) = t ^ 4
      rw [map_mul, hT, hS]
      group
    · change modularTraceProjectiveQuotientMap ModularGroup.T⁻¹ = t ^ 5
      rw [map_inv, hT, hinv]
  · fin_cases r
    · change modularTraceProjectiveQuotientMap 1 = t ^ 0
      simp only [map_one, pow_zero]
    · change modularTraceProjectiveQuotientMap ModularGroup.T = t ^ 1
      simpa only [pow_one] using hT
    · change modularTraceProjectiveQuotientMap
        (ModularGroup.T⁻¹ * ModularGroup.S) = t ^ 2
      rw [map_mul, map_inv, hT, hinv, hS, ← pow_add, hmod 8]
    · change modularTraceProjectiveQuotientMap ModularGroup.S = t ^ 3
      exact hS
    · change modularTraceProjectiveQuotientMap
        (ModularGroup.S * ModularGroup.T) = t ^ 4
      rw [map_mul, hS, hT]
      group
    · change modularTraceProjectiveQuotientMap
        (ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.S) = t ^ 5
      rw [map_mul, map_mul, map_inv, hS, hT, hinv, ← pow_add, ← pow_add, hmod 11]

/-- Equal projective trace-coset labels give equal actual orbit points.
The two possible central signs are treated explicitly. -/
theorem modularTraceQuotientMk_smul_eq_of_label_eq (g h : SL(2, ℤ))
    (heq : modularTraceProjectiveQuotientMap g = modularTraceProjectiveQuotientMap h)
    (z : UpperHalfPlane) :
    modularTraceQuotientMk (g • z) = modularTraceQuotientMk (h • z) := by
  let a : SL(2, ℤ) := g * h⁻¹
  have hqa : modularTraceProjectiveQuotientMap a = 1 := by
    simp only [a, map_mul, map_inv, heq, mul_inv_cancel]
  have hact : a • (h • z) = g • z := by simp only [a, mul_smul, inv_smul_smul]
  rcases (modularTraceProjectiveQuotientMap_eq_one_iff a).mp hqa with ha | ha
  · exact (congrArg modularTraceQuotientMk hact.symm).trans
      (modularTraceQuotientMk_ambient_smul a ha (h • z))
  · have hact' : (-a) • (h • z) = g • z := by
      rw [ModularGroup.SL_neg_smul]
      exact hact
    exact (congrArg modularTraceQuotientMk hact'.symm).trans
      (modularTraceQuotientMk_ambient_smul (-a) ha (h • z))

/-- The literal paper quadrilateral genuinely covers the actual trace quotient. -/
theorem paperIdealQuadrilateral_quotient_coverage (x : ModularTraceQuotient) :
    ∃ z ∈ paperIdealQuadrilateral, modularTraceQuotientMk z = x := by
  obtain ⟨r, w, hw, hrep⟩ := modularTraceQuotient_fd_representative x
  by_cases hleft : w.re ≤ 0
  · refine ⟨paperQuadrilateralCutWord r true • w,
      paperQuadrilateralCutWord_mem r true w hw hleft, ?_⟩
    apply Eq.trans _ hrep
    apply modularTraceQuotientMk_smul_eq_of_label_eq
    simpa only [map_pow, modularTraceProjectiveQuotientT] using
      paperQuadrilateralCutWord_quotient r true
  · have hright : 0 ≤ w.re := (lt_of_not_ge hleft).le
    refine ⟨paperQuadrilateralCutWord r false • w,
      paperQuadrilateralCutWord_mem r false w hw hright, ?_⟩
    apply Eq.trans _ hrep
    apply modularTraceQuotientMk_smul_eq_of_label_eq
    simpa only [map_pow, modularTraceProjectiveQuotientT] using
      paperQuadrilateralCutWord_quotient r false

end Markov
