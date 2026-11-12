import Markov.HyperbolicAxesSignCrossing
import Markov.PaperQuadrilateralSideHalfplanes

/-! Explicit original-side charts turn genuine geodesic crossings into sign
changes of the actual cell-defining functions. No transition field is supplied. -/
noncomputable section
open Set Topology
open scoped MatrixGroups
namespace Markov

/-- Literal integral SL side charts T, T^-1, A*T and B*T^-1. -/
def paperQuadrilateralSideChart (k : Fin 4) : SL(2, ℤ) :=
  ![ModularGroup.T, ModularGroup.T⁻¹, paperGeneratorASL * ModularGroup.T,
    paperGeneratorBSL * ModularGroup.T⁻¹] k

private theorem sideCrossing_Tinv_smul (z : UpperHalfPlane) :
    ModularGroup.T⁻¹ • z = (-1 : ℝ) +ᵥ z := by
  simpa only [zpow_neg_one, Int.cast_neg, Int.cast_one] using
    UpperHalfPlane.modular_T_zpow_smul z (-1)

/-- The literal side charts parametrize the already checked original side lines. -/
theorem paperQuadrilateralSideChart_vertical (k : Fin 4) (t : ℝ) :
    paperQuadrilateralSideChart k • hyperbolicVerticalAxis t =
      paperQuadrilateralGeodesicSideLine k t := by
  fin_cases k
  · change ModularGroup.T • hyperbolicVerticalAxis t = (1 : ℝ) +ᵥ hyperbolicVerticalAxis t
    exact UpperHalfPlane.modular_T_smul _
  · change ModularGroup.T⁻¹ • hyperbolicVerticalAxis t = (-1 : ℝ) +ᵥ hyperbolicVerticalAxis t
    exact sideCrossing_Tinv_smul _
  · change (paperGeneratorASL * ModularGroup.T) • hyperbolicVerticalAxis t =
      paperGeneratorASL • ((1 : ℝ) +ᵥ hyperbolicVerticalAxis t)
    rw [mul_smul, UpperHalfPlane.modular_T_smul]
  · change (paperGeneratorBSL * ModularGroup.T⁻¹) • hyperbolicVerticalAxis t =
      paperGeneratorBSL • ((-1 : ℝ) +ᵥ hyperbolicVerticalAxis t)
    rw [mul_smul, sideCrossing_Tinv_smul]

private theorem sideCrossing_real_inv_smul (h : SL(2, ℤ)) (z : UpperHalfPlane) :
    (h : SL(2, ℝ))⁻¹ • z = h⁻¹ • z := by
  calc
    _ = (h : SL(2, ℝ))⁻¹ • (h • (h⁻¹ • z)) := by rw [smul_inv_smul]
    _ = (h : SL(2, ℝ))⁻¹ • ((h : SL(2, ℝ)) • (h⁻¹ • z)) := by
      rw [modularInteger_smul_eq_real]
    _ = _ := inv_smul_smul _ _

private theorem sideCrossing_Aden_pos (z : UpperHalfPlane) : 0 < (2-z.re)^2+z.im^2 := by
  nlinarith [sq_nonneg (2-z.re), sq_pos_of_pos z.im_pos]

private theorem sideCrossing_Bden_pos (z : UpperHalfPlane) : 0 < (z.re+2)^2+z.im^2 := by
  nlinarith [sq_nonneg (z.re+2), sq_pos_of_pos z.im_pos]

private theorem sideCrossing_function_product_neg
    (k : Fin 4) (z w : UpperHalfPlane)
    (hprod : ((paperQuadrilateralSideChart k)⁻¹ • z).re *
      ((paperQuadrilateralSideChart k)⁻¹ • w).re < 0) :
    paperQuadrilateralSideFunction k z * paperQuadrilateralSideFunction k w < 0 := by
  fin_cases k
  · change (ModularGroup.T⁻¹ • z).re * (ModularGroup.T⁻¹ • w).re < 0 at hprod
    rw [sideCrossing_Tinv_smul, sideCrossing_Tinv_smul, UpperHalfPlane.vadd_re,
      UpperHalfPlane.vadd_re] at hprod
    change (1-z.re)*(1-w.re) < 0
    nlinarith only [hprod]
  · change ((ModularGroup.T⁻¹)⁻¹ • z).re * ((ModularGroup.T⁻¹)⁻¹ • w).re < 0 at hprod
    rw [inv_inv, UpperHalfPlane.modular_T_smul, UpperHalfPlane.modular_T_smul,
      UpperHalfPlane.vadd_re, UpperHalfPlane.vadd_re] at hprod
    change (z.re+1)*(w.re+1) < 0
    nlinarith only [hprod]
  · change ((paperGeneratorASL * ModularGroup.T)⁻¹ • z).re *
      ((paperGeneratorASL * ModularGroup.T)⁻¹ • w).re < 0 at hprod
    rw [mul_inv_rev, mul_smul, mul_smul, sideCrossing_Tinv_smul, sideCrossing_Tinv_smul,
      UpperHalfPlane.vadd_re, UpperHalfPlane.vadd_re] at hprod
    have hz := paperGeneratorA_circle_identity (paperGeneratorASL⁻¹ • z)
    have hw := paperGeneratorA_circle_identity (paperGeneratorASL⁻¹ • w)
    rw [smul_inv_smul] at hz hw
    change (z.re^2+z.re+z.im^2)*(w.re^2+w.re+w.im^2) < 0
    rw [hz, hw, div_mul_div_comm]
    apply div_neg_of_neg_of_pos _
      (mul_pos (sideCrossing_Aden_pos (paperGeneratorASL⁻¹ • z))
        (sideCrossing_Aden_pos (paperGeneratorASL⁻¹ • w)))
    nlinarith only [hprod]
  · change ((paperGeneratorBSL * ModularGroup.T⁻¹)⁻¹ • z).re *
      ((paperGeneratorBSL * ModularGroup.T⁻¹)⁻¹ • w).re < 0 at hprod
    rw [mul_inv_rev, inv_inv, mul_smul, mul_smul,
      UpperHalfPlane.modular_T_smul, UpperHalfPlane.modular_T_smul,
      UpperHalfPlane.vadd_re, UpperHalfPlane.vadd_re] at hprod
    have hz := paperGeneratorB_circle_identity (paperGeneratorBSL⁻¹ • z)
    have hw := paperGeneratorB_circle_identity (paperGeneratorBSL⁻¹ • w)
    rw [smul_inv_smul] at hz hw
    change (z.re^2-z.re+z.im^2)*(w.re^2-w.re+w.im^2) < 0
    rw [hz, hw, div_mul_div_comm]
    apply div_neg_of_neg_of_pos _
      (mul_pos (sideCrossing_Bden_pos (paperGeneratorBSL⁻¹ • z))
        (sideCrossing_Bden_pos (paperGeneratorBSL⁻¹ • w)))
    nlinarith only [hprod]

/-- An actual isometric line meeting a noncoincident actual original side has
opposite actual cell-defining signs for all source parameters around the root. -/
theorem paperQuadrilateralSideFunction_isometric_crossing
    (F : ℝ → UpperHalfPlane) (hF : Isometry F) (k : Fin 4)
    (hne : Set.range F ≠ paperQuadrilateralGeodesicSide k)
    (t₀ : ℝ) (hroot : F t₀ ∈ paperQuadrilateralGeodesicSide k)
    (s u : ℝ) (hs : s < t₀) (hu : t₀ < u) :
    paperQuadrilateralSideFunction k (F s) * paperQuadrilateralSideFunction k (F u) < 0 := by
  let A : SL(2, ℝ) := (paperQuadrilateralSideChart k : SL(2, ℝ))
  have hrange : Set.range (fun t : ℝ => A • hyperbolicVerticalAxis t) =
      paperQuadrilateralGeodesicSide k := by
    have he : (fun t : ℝ => A • hyperbolicVerticalAxis t) =
        paperQuadrilateralGeodesicSideLine k := by
      funext t
      rw [← paperQuadrilateralSideChart_vertical, modularInteger_smul_eq_real]
    rw [he, paperQuadrilateralGeodesicSideLine_range]
  have hroot' : (A⁻¹ • F t₀).re = 0 := by
    obtain ⟨v, hv⟩ := hrange.symm ▸ hroot
    rw [← hv, inv_smul_smul]
    rfl
  have hp := upperHalfPlane_isometric_line_crosses_SL_axis A F hF
    (by simpa only [hrange] using hne) t₀ hroot' s u hs hu
  apply sideCrossing_function_product_neg k (F s) (F u)
  simpa only [A, sideCrossing_real_inv_smul] using hp

end Markov
