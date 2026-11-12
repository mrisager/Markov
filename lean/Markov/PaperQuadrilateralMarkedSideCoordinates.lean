import Markov.PaperQuadrilateralOppositeGluing

/-! Actual marked-square coordinates on the four literal original Q sides.
The varying coordinate determines the actual point and lies strictly in(-1,1).
No finite ordering is assumed. -/
noncomputable section
open Set
namespace Markov

/-- The literal square side point in original side order top,right,bottom,left. -/
def paperQuadrilateralMarkedSidePoint (k : Fin 4) (r : ℝ) : ℝ × ℝ :=
  ![(r, 1), (1, r), (r, -1), (-1, r)] k

private theorem markedSide_bottom (z : paperIdealQuadrilateral)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide 2) :
    (paperMarkedQuadrilateralSquareHomeomorph z).val.2 = -1 := by
  obtain ⟨t, ht⟩ := (paperQuadrilateralGeodesicSideLine_range 2 ▸ hz)
  have hu : paperQuadrilateralGeodesicSideLine 0 t ∈ paperQuadrilateralGeodesicSide 0 := by
    rw [← paperQuadrilateralGeodesicSideLine_range]
    exact ⟨t, rfl⟩
  let u : paperIdealQuadrilateral := ⟨paperQuadrilateralGeodesicSideLine 0 t,
    paperQuadrilateralGeodesicSide_subset 0 hu⟩
  have hact : paperGeneratorASL • u.val = z.val := ht
  exact congrArg Prod.snd (paperMarkedSquare_A_pair u z hu hact).2

private theorem markedSide_left (z : paperIdealQuadrilateral)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide 3) :
    (paperMarkedQuadrilateralSquareHomeomorph z).val.1 = -1 := by
  obtain ⟨t, ht⟩ := (paperQuadrilateralGeodesicSideLine_range 3 ▸ hz)
  have hu : paperQuadrilateralGeodesicSideLine 1 t ∈ paperQuadrilateralGeodesicSide 1 := by
    rw [← paperQuadrilateralGeodesicSideLine_range]
    exact ⟨t, rfl⟩
  let u : paperIdealQuadrilateral := ⟨paperQuadrilateralGeodesicSideLine 1 t,
    paperQuadrilateralGeodesicSide_subset 1 hu⟩
  have hact : paperGeneratorBSL • u.val = z.val := ht
  exact congrArg Prod.fst (paperMarkedSquare_B_pair u z hu hact).2

/-- Every actual original-side point has the displayed literal marked-square shape. -/
theorem paperQuadrilateralMarkedSideCoordinate_shape (k : Fin 4) (z : paperIdealQuadrilateral)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide k) :
    (paperMarkedQuadrilateralSquareHomeomorph z).val =
      paperQuadrilateralMarkedSidePoint k (paperQuadrilateralMarkedSideCoordinate k z) := by
  fin_cases k
  · exact Prod.ext rfl ((paperMarkedSquare_top_iff z).mpr hz)
  · exact Prod.ext ((paperMarkedSquare_right_iff z).mpr hz) rfl
  · exact Prod.ext rfl (markedSide_bottom z hz)
  · exact Prod.ext (markedSide_left z hz) rfl

/-- The actual free side coordinate lies strictly between the deleted corners. -/
theorem paperQuadrilateralMarkedSideCoordinate_bounds (k : Fin 4) (z : paperIdealQuadrilateral)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide k) :
    -1 < paperQuadrilateralMarkedSideCoordinate k z ∧
      paperQuadrilateralMarkedSideCoordinate k z < 1 := by
  have hs := paperQuadrilateralMarkedSideCoordinate_shape k z hz
  fin_cases k
  · exact paperPuncturedSquare_horizontal_param _ (Or.inl (congrArg Prod.snd hs))
  · exact paperPuncturedSquare_vertical_param _ (Or.inl (congrArg Prod.fst hs))
  · exact paperPuncturedSquare_horizontal_param _ (Or.inr (congrArg Prod.snd hs))
  · exact paperPuncturedSquare_vertical_param _ (Or.inr (congrArg Prod.fst hs))

/-- On each literal side, equality of actual marked coordinates implies equality
of the actual Q-points through the actual marked-square homeomorphism. -/
theorem paperQuadrilateralMarkedSideCoordinate_injective (k : Fin 4)
    (z w : paperIdealQuadrilateral)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide k)
    (hw : w.val ∈ paperQuadrilateralGeodesicSide k)
    (he : paperQuadrilateralMarkedSideCoordinate k z =
      paperQuadrilateralMarkedSideCoordinate k w) : z = w := by
  apply paperMarkedQuadrilateralSquareHomeomorph.injective
  apply Subtype.ext
  rw [paperQuadrilateralMarkedSideCoordinate_shape k z hz,
    paperQuadrilateralMarkedSideCoordinate_shape k w hw, he]

end Markov
