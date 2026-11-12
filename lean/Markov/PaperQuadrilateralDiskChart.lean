import Markov.PaperQuadrilateralFrontierExact
import Markov.PaperQuadrilateralSquareEdges
import Markov.ConvexDiskRadialObstruction

/-! An actual disk coordinate for the literal original quadrilateral. It is
constructed from the checked actual square homeomorphism and the checked
actual radial gauge homeomorphism. Frontier and strict-interior transport are
proved, not introduced as assumed boundary-order or winding fields. -/

noncomputable section
open Set Topology Metric
namespace Markov

private def paperComplexSquareBox : Set ℂ := Icc (-1) 1 ×ℂ Icc (-1) 1

private theorem paperComplexSquareBox_convex : Convex ℝ paperComplexSquareBox := by
  change Convex ℝ (Complex.equivRealProdLm ⁻¹' (Icc (-1) 1 ×ˢ Icc (-1) 1))
  exact ((convex_Icc (-1) 1).prod (convex_Icc (-1) 1)).linear_preimage
    Complex.equivRealProdLm.toLinearMap

private theorem paperComplexSquareBox_closed : IsClosed paperComplexSquareBox :=
  isClosed_Icc.reProdIm isClosed_Icc

private theorem paperComplexSquareBox_bounded : Bornology.IsBounded paperComplexSquareBox :=
  (isBounded_Icc (-1) 1).reProdIm (isBounded_Icc (-1) 1)

private theorem paperComplexSquareBox_nhds : paperComplexSquareBox ∈ 𝓝 0 := by
  apply mem_interior_iff_mem_nhds.mp
  rw [paperComplexSquareBox, Complex.interior_reProdIm, interior_Icc]
  change ((-1:ℝ) < 0 ∧ 0 < (1:ℝ)) ∧ ((-1:ℝ) < 0 ∧ 0 < (1:ℝ))
  norm_num

private def paperComplexSquareRadial : ℂ ≃ₜ ℂ :=
  convexDiskRadialHomeomorph paperComplexSquareBox paperComplexSquareBox_convex
    paperComplexSquareBox_nhds paperComplexSquareBox_bounded

/-- The actual raw square chart, viewed literally as one complex coordinate. -/
def paperQuadrilateralComplexSquare (z : paperIdealQuadrilateral) : ℂ :=
  ⟨paperSquareChartA z, paperSquareChartB z⟩

theorem continuous_paperQuadrilateralComplexSquare : Continuous paperQuadrilateralComplexSquare := by
  exact Complex.equivRealProdCLM.symm.continuous.comp
    ((continuous_paperSquareChartA.comp continuous_subtype_val).prodMk
      (continuous_paperSquareChartB.comp continuous_subtype_val))

private theorem paperQuadrilateralComplexSquare_mem (z : paperIdealQuadrilateral) :
    paperQuadrilateralComplexSquare z ∈ paperComplexSquareBox := by
  have h := paperSquareChart_mem z
  exact ⟨abs_le.mp h.1, abs_le.mp h.2.1⟩

private theorem paperQuadrilateralComplexSquare_frontier (z : paperIdealQuadrilateral)
    (hz : (z:UpperHalfPlane) ∈ frontier paperIdealQuadrilateral) :
    paperQuadrilateralComplexSquare z ∈ frontier paperComplexSquareBox := by
  refine ⟨subset_closure (paperQuadrilateralComplexSquare_mem z), ?_⟩
  intro hi
  rw [paperComplexSquareBox, Complex.interior_reProdIm, interior_Icc] at hi
  change (-1 < paperSquareChartA z ∧ paperSquareChartA z < 1) ∧
    (-1 < paperSquareChartB z ∧ paperSquareChartB z < 1) at hi
  obtain ⟨k, hk⟩ := mem_iUnion.mp (paperIdealQuadrilateral_frontier_eq_sides ▸ hz)
  fin_cases k
  · have h := (paperSquareChartB_eq_one_iff z).mpr hk
    linarith [hi.2.2]
  · have h := (paperSquareChartA_eq_one_iff z).mpr hk
    linarith [hi.1.2]
  · have h := (paperSquareChartB_eq_neg_one_iff z).mpr hk
    linarith [hi.2.1]
  · have h := (paperSquareChartA_eq_neg_one_iff z).mpr hk
    linarith [hi.1.1]

private theorem paperQuadrilateralComplexSquare_interior (z : paperIdealQuadrilateral)
    (hz : (z:UpperHalfPlane) ∈ paperIdealQuadrilateralStrictRegion) :
    paperQuadrilateralComplexSquare z ∈ interior paperComplexSquareBox := by
  have hside (k : Fin 4) : (z:UpperHalfPlane) ∉ paperQuadrilateralGeodesicSide k :=
    fun hk => (paperQuadrilateralGeodesicSide_subset_frontier k hk).2
      (paperIdealQuadrilateralStrictRegion_subset_interior hz)
  have hA1 : paperSquareChartA z ≠ 1 :=
    fun h => hside 1 ((paperSquareChartA_eq_one_iff z).mp h)
  have hAm : paperSquareChartA z ≠ -1 :=
    fun h => hside 3 ((paperSquareChartA_eq_neg_one_iff z).mp h)
  have hB1 : paperSquareChartB z ≠ 1 :=
    fun h => hside 0 ((paperSquareChartB_eq_one_iff z).mp h)
  have hBm : paperSquareChartB z ≠ -1 :=
    fun h => hside 2 ((paperSquareChartB_eq_neg_one_iff z).mp h)
  have h := paperSquareChart_mem z
  obtain ⟨hAl, hAr⟩ := abs_le.mp h.1
  obtain ⟨hBl, hBr⟩ := abs_le.mp h.2.1
  rw [paperComplexSquareBox, Complex.interior_reProdIm, interior_Icc]
  exact ⟨⟨lt_of_le_of_ne hAl hAm.symm, lt_of_le_of_ne hAr hA1⟩,
    ⟨lt_of_le_of_ne hBl hBm.symm, lt_of_le_of_ne hBr hB1⟩⟩

private theorem paperComplexSquareRadial_image_ball :
    paperComplexSquareRadial '' ball (0:ℂ) 1 = interior paperComplexSquareBox := by
  have h := paperComplexSquareRadial.image_interior (closedBall (0:ℂ) 1)
  rw [interior_closedBall (0:ℂ) (by norm_num : (1:ℝ) ≠ 0)] at h
  have he : paperComplexSquareRadial '' closedBall (0:ℂ) 1 = closure paperComplexSquareBox :=
    convexDiskRadialHomeomorph_image_closedBall _ _ _ _
  rw [he, paperComplexSquareBox_closed.closure_eq] at h
  exact h

/-- The actual quadrilateral disk coordinate is inverse radial rescaling of
its literal raw square coordinate. Its four omitted ideal vertices are not
adjoined to the domain. -/
def paperQuadrilateralDiskCoordinate (z : paperIdealQuadrilateral) : ℂ :=
  paperComplexSquareRadial.symm (paperQuadrilateralComplexSquare z)

theorem continuous_paperQuadrilateralDiskCoordinate : Continuous paperQuadrilateralDiskCoordinate :=
  paperComplexSquareRadial.symm.continuous.comp continuous_paperQuadrilateralComplexSquare

/-- This is an actual injective coordinate, not a boundary-order assumption. -/
theorem paperQuadrilateralDiskCoordinate_injective : Function.Injective paperQuadrilateralDiskCoordinate := by
  intro z w heq
  have hc := paperComplexSquareRadial.symm.injective heq
  apply paperQuadrilateralSquareHomeomorph.injective
  apply Subtype.ext
  exact Prod.ext (congrArg Complex.re hc) (congrArg Complex.im hc)

/-- Every actual closed-Q point has a closed-unit-disk coordinate. -/
theorem paperQuadrilateralDiskCoordinate_norm_le_one (z : paperIdealQuadrilateral) :
    ‖paperQuadrilateralDiskCoordinate z‖ ≤ 1 := by
  have he : paperComplexSquareRadial '' closedBall (0:ℂ) 1 = closure paperComplexSquareBox :=
    convexDiskRadialHomeomorph_image_closedBall _ _ _ _
  have hm : paperQuadrilateralComplexSquare z ∈ paperComplexSquareRadial '' closedBall (0:ℂ) 1 := by
    rw [he]
    exact subset_closure (paperQuadrilateralComplexSquare_mem z)
  obtain ⟨w, hw, heq⟩ := hm
  change ‖paperComplexSquareRadial.symm (paperQuadrilateralComplexSquare z)‖ ≤ 1
  rw [← heq, Homeomorph.symm_apply_apply]
  simpa only [mem_closedBall, dist_zero_right] using hw

/-- Genuine original-Q frontier maps to the actual complex unit circle. -/
theorem paperQuadrilateralDiskCoordinate_norm_eq_one_of_frontier
    (z : paperIdealQuadrilateral) (hz : (z:UpperHalfPlane) ∈ frontier paperIdealQuadrilateral) :
    ‖paperQuadrilateralDiskCoordinate z‖ = 1 := by
  have he : paperComplexSquareRadial '' sphere (0:ℂ) 1 = frontier paperComplexSquareBox :=
    convexDiskRadialHomeomorph_image_frontier _ _ _ _
  have hm : paperQuadrilateralComplexSquare z ∈ paperComplexSquareRadial '' sphere (0:ℂ) 1 := by
    rw [he]
    exact paperQuadrilateralComplexSquare_frontier z hz
  obtain ⟨w, hw, heq⟩ := hm
  change ‖paperComplexSquareRadial.symm (paperQuadrilateralComplexSquare z)‖ = 1
  rw [← heq, Homeomorph.symm_apply_apply]
  simpa only [mem_sphere, dist_zero_right] using hw

/-- The actual strict original-Q region maps into the actual OPEN unit disk. -/
theorem paperQuadrilateralDiskCoordinate_norm_lt_one_of_strict
    (z : paperIdealQuadrilateral) (hz : (z:UpperHalfPlane) ∈ paperIdealQuadrilateralStrictRegion) :
    ‖paperQuadrilateralDiskCoordinate z‖ < 1 := by
  have hm : paperQuadrilateralComplexSquare z ∈ paperComplexSquareRadial '' ball (0:ℂ) 1 := by
    rw [paperComplexSquareRadial_image_ball]
    exact paperQuadrilateralComplexSquare_interior z hz
  obtain ⟨w, hw, heq⟩ := hm
  change ‖paperComplexSquareRadial.symm (paperQuadrilateralComplexSquare z)‖ < 1
  rw [← heq, Homeomorph.symm_apply_apply]
  simpa only [mem_ball, dist_zero_right] using hw

end Markov
