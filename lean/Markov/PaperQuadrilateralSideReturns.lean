import Markov.PaperQuadrilateralInversion

noncomputable section
open scoped MatrixGroups
namespace Markov

theorem paperGeneratorA_quadrilateral_return_iff (z : UpperHalfPlane)
    (hz : z ∈ paperIdealQuadrilateral) :
    paperGeneratorASL • z ∈ paperIdealQuadrilateral ↔ z ∈ paperRightVerticalSide := by
  constructor
  · intro hw
    have hD : 0 < (2 - z.re) ^ 2 + z.im ^ 2 := by
      nlinarith [sq_nonneg (2 - z.re), sq_pos_of_pos z.im_pos]
    have hw' : 0 ≤ (z.re - 1) / ((2 - z.re) ^ 2 + z.im ^ 2) := by
      rw [← paperGeneratorA_circle_identity]
      exact hw.2.2.1
    have hx : 0 ≤ z.re - 1 := by simpa only [zero_mul] using (le_div_iff₀ hD).mp hw'
    change z.re = 1
    linarith [hz.2.1]
  · intro hside
    exact paperLeftSemicircleSide_subset_quadrilateral ((paperGeneratorA_side_iff z).mpr hside)

theorem paperGeneratorB_quadrilateral_return_iff (z : UpperHalfPlane)
    (hz : z ∈ paperIdealQuadrilateral) :
    paperGeneratorBSL • z ∈ paperIdealQuadrilateral ↔ z ∈ paperLeftVerticalSide := by
  constructor
  · intro hw
    have hD : 0 < (z.re + 2) ^ 2 + z.im ^ 2 := by
      nlinarith [sq_nonneg (z.re + 2), sq_pos_of_pos z.im_pos]
    have hw' : 0 ≤ -(z.re + 1) / ((z.re + 2) ^ 2 + z.im ^ 2) := by
      rw [← paperGeneratorB_circle_identity]
      exact hw.2.2.2
    have hx : 0 ≤ -(z.re + 1) := by simpa only [zero_mul] using (le_div_iff₀ hD).mp hw'
    change z.re = -1
    linarith [hz.1]
  · intro hside
    exact paperRightSemicircleSide_subset_quadrilateral ((paperGeneratorB_side_iff z).mpr hside)

theorem paperGeneratorA_inv_quadrilateral_return_iff (z : UpperHalfPlane)
    (hz : z ∈ paperIdealQuadrilateral) :
    paperGeneratorASL⁻¹ • z ∈ paperIdealQuadrilateral ↔ z ∈ paperLeftSemicircleSide := by
  constructor
  · intro hw
    have hside : paperGeneratorASL⁻¹ • z ∈ paperRightVerticalSide :=
      (paperGeneratorA_quadrilateral_return_iff _ hw).mp (by simpa only [smul_inv_smul] using hz)
    exact (paperGeneratorA_inv_side_iff z).mp hside
  · intro hside
    exact paperRightVerticalSide_subset_quadrilateral ((paperGeneratorA_inv_side_iff z).mpr hside)

theorem paperGeneratorB_inv_quadrilateral_return_iff (z : UpperHalfPlane)
    (hz : z ∈ paperIdealQuadrilateral) :
    paperGeneratorBSL⁻¹ • z ∈ paperIdealQuadrilateral ↔ z ∈ paperRightSemicircleSide := by
  constructor
  · intro hw
    have hside : paperGeneratorBSL⁻¹ • z ∈ paperLeftVerticalSide :=
      (paperGeneratorB_quadrilateral_return_iff _ hw).mp (by simpa only [smul_inv_smul] using hz)
    exact (paperGeneratorB_inv_side_iff z).mp hside
  · intro hside
    exact paperLeftVerticalSide_subset_quadrilateral ((paperGeneratorB_inv_side_iff z).mpr hside)

theorem paperIdealQuadrilateral_T_three_not_mem (z : UpperHalfPlane)
    (hz : z ∈ paperIdealQuadrilateral) :
    ModularGroup.T ^ 3 • z ∉ paperIdealQuadrilateral := by
  intro hw
  have hre : (ModularGroup.T ^ 3 • z).re = z.re + 3 := by
    have h := congrArg UpperHalfPlane.re (UpperHalfPlane.modular_T_zpow_smul z (3 : ℤ))
    simpa only [zpow_ofNat, Int.cast_ofNat, add_comm] using h
  have hw' := hw.2.1
  rw [hre] at hw'
  linarith [hz.1]

theorem paperIdealQuadrilateral_T_three_inv_not_mem (z : UpperHalfPlane)
    (hz : z ∈ paperIdealQuadrilateral) :
    (ModularGroup.T ^ 3)⁻¹ • z ∉ paperIdealQuadrilateral := by
  intro hw
  apply paperIdealQuadrilateral_T_three_not_mem ((ModularGroup.T ^ 3)⁻¹ • z) hw
  simpa only [smul_inv_smul] using hz

theorem paperIdealQuadrilateral_T_three_S_not_mem (z : UpperHalfPlane)
    (hz : z ∈ paperIdealQuadrilateral) :
    (ModularGroup.T ^ 3 * ModularGroup.S) • z ∉ paperIdealQuadrilateral := by
  rw [mul_smul]
  exact paperIdealQuadrilateral_T_three_not_mem _ ((paperIdealQuadrilateral_S_mem_iff z).mpr hz)

theorem paperIdealQuadrilateral_T_three_inv_S_not_mem (z : UpperHalfPlane)
    (hz : z ∈ paperIdealQuadrilateral) :
    ((ModularGroup.T ^ 3)⁻¹ * ModularGroup.S) • z ∉ paperIdealQuadrilateral := by
  rw [mul_smul]
  exact paperIdealQuadrilateral_T_three_inv_not_mem _ ((paperIdealQuadrilateral_S_mem_iff z).mpr hz)

theorem paperIdealQuadrilateral_S_T_three_not_mem (z : UpperHalfPlane)
    (hz : z ∈ paperIdealQuadrilateral) :
    (ModularGroup.S * ModularGroup.T ^ 3) • z ∉ paperIdealQuadrilateral := by
  rw [mul_smul, paperIdealQuadrilateral_S_mem_iff]
  exact paperIdealQuadrilateral_T_three_not_mem z hz

theorem paperIdealQuadrilateral_S_T_three_inv_not_mem (z : UpperHalfPlane)
    (hz : z ∈ paperIdealQuadrilateral) :
    (ModularGroup.S * (ModularGroup.T ^ 3)⁻¹) • z ∉ paperIdealQuadrilateral := by
  rw [mul_smul, paperIdealQuadrilateral_S_mem_iff]
  exact paperIdealQuadrilateral_T_three_inv_not_mem z hz

end Markov

