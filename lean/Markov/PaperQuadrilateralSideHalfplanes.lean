import Markov.PaperQuadrilateralSideAdjacency

/-! Actual defining half-planes of original and neighboring cells, and their
strict local membership consequences. All functions and deck cells are literal. -/
noncomputable section
open Set Topology
namespace Markov

/-- The four literal side-defining functions, positive toward the original cell. -/
def paperQuadrilateralSideFunction (k : Fin 4) (z : UpperHalfPlane) : ℝ :=
  ![1 - z.re, z.re + 1, z.re ^ 2 + z.re + z.im ^ 2,
    z.re ^ 2 - z.re + z.im ^ 2] k

theorem paperQuadrilateralSideFunction_continuous (k : Fin 4) :
    Continuous (paperQuadrilateralSideFunction k) := by
  fin_cases k
  · change Continuous (fun z : UpperHalfPlane => 1 - z.re)
    fun_prop
  · change Continuous (fun z : UpperHalfPlane => z.re + 1)
    fun_prop
  · change Continuous (fun z : UpperHalfPlane => z.re ^ 2 + z.re + z.im ^ 2)
    fun_prop
  · change Continuous (fun z : UpperHalfPlane => z.re ^ 2 - z.re + z.im ^ 2)
    fun_prop

theorem paperQuadrilateralSideFunction_nonneg
    (k : Fin 4) (z : UpperHalfPlane) (hz : z ∈ paperIdealQuadrilateral) :
    0 ≤ paperQuadrilateralSideFunction k z := by
  fin_cases k
  · exact sub_nonneg.mpr hz.2.1
  · dsimp [paperQuadrilateralSideFunction]
    linarith [hz.1]
  · exact hz.2.2.1
  · exact hz.2.2.2

theorem paperQuadrilateralSideFunction_eq_zero_iff (k : Fin 4) (z : UpperHalfPlane) :
    paperQuadrilateralSideFunction k z = 0 ↔ z ∈ paperQuadrilateralGeodesicSide k := by
  fin_cases k
  · change 1 - z.re = 0 ↔ z.re = 1
    exact sub_eq_zero.trans eq_comm
  · change z.re + 1 = 0 ↔ z.re = -1
    exact add_eq_zero_iff_eq_neg
  · rfl
  · rfl

private theorem halfplane_Aden_pos (z : UpperHalfPlane) : 0 < (2-z.re)^2+z.im^2 := by
  nlinarith [sq_nonneg (2-z.re), sq_pos_of_pos z.im_pos]

private theorem halfplane_Bden_pos (z : UpperHalfPlane) : 0 < (z.re+2)^2+z.im^2 := by
  nlinarith [sq_nonneg (z.re+2), sq_pos_of_pos z.im_pos]

/-- The actual paired neighboring cell lies on the opposite closed side of
the actual supporting geodesic, proved from the original A/B circle identities. -/
theorem paperQuadrilateralSideFunction_nonpos_neighbor
    (k : Fin 4) (z : UpperHalfPlane)
    (hz : z ∈ (fun w : UpperHalfPlane => paperQuadrilateralSideNeighbor k • w) ''
      paperIdealQuadrilateral) : paperQuadrilateralSideFunction k z ≤ 0 := by
  obtain ⟨w, hw, rfl⟩ := hz
  fin_cases k
  · let z := paperGeneratorASL⁻¹ • w
    have hAz : paperGeneratorASL • z = w := smul_inv_smul _ _
    have hp := hw.2.2.1
    rw [← hAz, paperGeneratorA_circle_identity] at hp
    have hn := (le_div_iff₀ (halfplane_Aden_pos z)).mp hp
    change 1 - z.re ≤ 0
    linarith
  · let z := paperGeneratorBSL⁻¹ • w
    have hBz : paperGeneratorBSL • z = w := smul_inv_smul _ _
    have hp := hw.2.2.2
    rw [← hBz, paperGeneratorB_circle_identity] at hp
    have hn := (le_div_iff₀ (halfplane_Bden_pos z)).mp hp
    change z.re + 1 ≤ 0
    linarith
  · change (paperGeneratorASL • w).re ^ 2 + (paperGeneratorASL • w).re +
      (paperGeneratorASL • w).im ^ 2 ≤ 0
    rw [paperGeneratorA_circle_identity]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hw.2.1]) (halfplane_Aden_pos w).le
  · change (paperGeneratorBSL • w).re ^ 2 - (paperGeneratorBSL • w).re +
      (paperGeneratorBSL • w).im ^ 2 ≤ 0
    rw [paperGeneratorB_circle_identity]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hw.1]) (halfplane_Bden_pos w).le

/-- In an actual open two-cell neighborhood, the positive and negative literal
side-function regions lie in the respective genuine cell interiors. -/
theorem paperQuadrilateral_side_local_strict_halfplanes
    (k : Fin 4) (z : UpperHalfPlane) (hz : z ∈ paperQuadrilateralGeodesicSide k) :
    ∃ U : Set UpperHalfPlane, IsOpen U ∧ z ∈ U ∧
      (∀ w ∈ U, 0 < paperQuadrilateralSideFunction k w →
        w ∈ interior paperIdealQuadrilateral) ∧
      (∀ w ∈ U, paperQuadrilateralSideFunction k w < 0 →
        w ∈ (fun v : UpperHalfPlane => paperQuadrilateralSideNeighbor k • v) ''
          interior paperIdealQuadrilateral) := by
  obtain ⟨U, hU, hzU, hcover⟩ := paperQuadrilateral_side_local_adjacent_cover k z hz
  have hposOpen : IsOpen {w : UpperHalfPlane | 0 < paperQuadrilateralSideFunction k w} :=
    isOpen_lt continuous_const (paperQuadrilateralSideFunction_continuous k)
  have hnegOpen : IsOpen {w : UpperHalfPlane | paperQuadrilateralSideFunction k w < 0} :=
    isOpen_lt (paperQuadrilateralSideFunction_continuous k) continuous_const
  refine ⟨U, hU, hzU, ?_, ?_⟩
  · intro w hw hpos
    have hsub : U ∩ {v | 0 < paperQuadrilateralSideFunction k v} ⊆
        paperIdealQuadrilateral := by
      intro v hv
      rcases hcover hv.1 with hQ | hN
      · exact hQ
      · exact (not_lt_of_ge (paperQuadrilateralSideFunction_nonpos_neighbor k v hN) hv.2).elim
    exact interior_maximal hsub (hU.inter hposOpen) ⟨hw, hpos⟩
  · intro w hw hneg
    have hsub : U ∩ {v | paperQuadrilateralSideFunction k v < 0} ⊆
        (fun v : UpperHalfPlane => paperQuadrilateralSideNeighbor k • v) ''
          paperIdealQuadrilateral := by
      intro v hv
      rcases hcover hv.1 with hQ | hN
      · exact (not_lt_of_ge (paperQuadrilateralSideFunction_nonneg k v hQ) hv.2).elim
      · exact hN
    have hint := interior_maximal hsub (hU.inter hnegOpen) ⟨hw, hneg⟩
    change w ∈ (Homeomorph.smul (paperQuadrilateralSideNeighbor k)) ''
      interior paperIdealQuadrilateral
    rw [(Homeomorph.smul (paperQuadrilateralSideNeighbor k)).image_interior]
    exact hint

end Markov
