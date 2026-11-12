import Markov.PaperQuadrilateralSideAdjacency
import Markov.PaperQuadrilateralSideQuotient
import Markov.PaperMarkedSquareRelations

/-! Actual distinct original-Q points with the same actual quotient image
lie on opposite literal sides and have equal normalized marked-square free
coordinates. The four actual A/B return cases discharge the result; no
boundary pairing, side order, or coordinate preservation is assumed. -/

noncomputable section
namespace Markov

/-- The literal opposite-side permutation, in original side order
TOP, RIGHT, BOTTOM, LEFT =0,1,2,3. -/
def paperQuadrilateralOppositeSide : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp] theorem paperQuadrilateralOppositeSide_apply_apply (i : Fin 4) :
    paperQuadrilateralOppositeSide (paperQuadrilateralOppositeSide i) = i := by
  fin_cases i <;> rfl

/-- The actual marked-square free side coordinate: x on top/bottom, y on
right/left. The chart itself is the checked literal normalized chart. -/
def paperQuadrilateralMarkedSideCoordinate (k : Fin 4) (z : paperIdealQuadrilateral) : ℝ :=
  ![(paperMarkedQuadrilateralSquareHomeomorph z).val.1,
    (paperMarkedQuadrilateralSquareHomeomorph z).val.2,
    (paperMarkedQuadrilateralSquareHomeomorph z).val.1,
    (paperMarkedQuadrilateralSquareHomeomorph z).val.2] k

private theorem oppositeGluing_side_unique (i j : Fin 4) (z : UpperHalfPlane)
    (hi : z ∈ paperQuadrilateralGeodesicSide i)
    (hj : z ∈ paperQuadrilateralGeodesicSide j) : i=j := by
  by_contra hne
  exact Set.disjoint_left.mp (paperQuadrilateralGeodesicSides_disjoint i j hne) hi hj

/-- Genuine actual quotient equality of DISTINCT Q representatives forces the
opposite literal side index and exact marked-square free-coordinate equality.
Only actual matrix returns and actual A/B chart pairing theorems are used. -/
theorem paperQuadrilateral_distinct_projected_eq_opposite_and_coordinate
    (z w : paperIdealQuadrilateral) (hne : z ≠ w)
    (hproj : modularTraceQuotientMk z = modularTraceQuotientMk w)
    (i j : Fin 4)
    (hzi : (z:UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide i)
    (hwj : (w:UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide j) :
    j = paperQuadrilateralOppositeSide i ∧
      paperQuadrilateralMarkedSideCoordinate i z = paperQuadrilateralMarkedSideCoordinate j w := by
  obtain ⟨δ, hδ⟩ := (modularTraceQuotientMk_eq_iff w.val z.val).mp hproj.symm
  have hact : δ.val • z.val = w.val := hδ
  have hret : δ.val • z.val ∈ paperIdealQuadrilateral := hact.symm ▸ w.property
  rcases (paperIdealQuadrilateral_return_iff δ.val δ.property z.val z.property).mp hret with
    hidentity | ⟨hA, hzA⟩ | ⟨hAi, hzAi⟩ | ⟨hB, hzB⟩ | ⟨hBi, hzBi⟩
  · rw [hidentity, one_smul] at hact
    exact (hne (Subtype.ext hact)).elim
  · rw [hA] at hact
    have hw2 : w.val ∈ paperQuadrilateralGeodesicSide 2 := by
      rw [← hact]
      exact (paperGeneratorA_side_iff z.val).mpr hzA
    have hi : i=0 := oppositeGluing_side_unique i 0 z hzi hzA
    have hj : j=2 := oppositeGluing_side_unique j 2 w hwj hw2
    subst i
    subst j
    refine ⟨rfl, ?_⟩
    change (paperMarkedQuadrilateralSquareHomeomorph z).val.1 =
      (paperMarkedQuadrilateralSquareHomeomorph w).val.1
    exact ((paperMarkedSquare_A_pair_iff z w).mpr ⟨hzA, hact⟩).2.2
  · rw [hAi] at hact
    have hw0 : w.val ∈ paperQuadrilateralGeodesicSide 0 := by
      rw [← hact]
      exact (paperGeneratorA_inv_side_iff z.val).mpr hzAi
    have hforward : paperGeneratorASL • w.val = z.val := by rw [← hact, smul_inv_smul]
    have hi : i=2 := oppositeGluing_side_unique i 2 z hzi hzAi
    have hj : j=0 := oppositeGluing_side_unique j 0 w hwj hw0
    subst i
    subst j
    refine ⟨rfl, ?_⟩
    change (paperMarkedQuadrilateralSquareHomeomorph z).val.1 =
      (paperMarkedQuadrilateralSquareHomeomorph w).val.1
    exact ((paperMarkedSquare_A_pair_iff w z).mpr ⟨hw0, hforward⟩).2.2.symm
  · rw [hB] at hact
    have hw3 : w.val ∈ paperQuadrilateralGeodesicSide 3 := by
      rw [← hact]
      exact (paperGeneratorB_side_iff z.val).mpr hzB
    have hi : i=1 := oppositeGluing_side_unique i 1 z hzi hzB
    have hj : j=3 := oppositeGluing_side_unique j 3 w hwj hw3
    subst i
    subst j
    refine ⟨rfl, ?_⟩
    change (paperMarkedQuadrilateralSquareHomeomorph z).val.2 =
      (paperMarkedQuadrilateralSquareHomeomorph w).val.2
    exact ((paperMarkedSquare_B_pair_iff z w).mpr ⟨hzB, hact⟩).2.2
  · rw [hBi] at hact
    have hw1 : w.val ∈ paperQuadrilateralGeodesicSide 1 := by
      rw [← hact]
      exact (paperGeneratorB_inv_side_iff z.val).mpr hzBi
    have hforward : paperGeneratorBSL • w.val = z.val := by rw [← hact, smul_inv_smul]
    have hi : i=3 := oppositeGluing_side_unique i 3 z hzi hzBi
    have hj : j=1 := oppositeGluing_side_unique j 1 w hwj hw1
    subst i
    subst j
    refine ⟨rfl, ?_⟩
    change (paperMarkedQuadrilateralSquareHomeomorph z).val.2 =
      (paperMarkedQuadrilateralSquareHomeomorph w).val.2
    exact ((paperMarkedSquare_B_pair_iff w z).mpr ⟨hw1, hforward⟩).2.2.symm

end Markov
