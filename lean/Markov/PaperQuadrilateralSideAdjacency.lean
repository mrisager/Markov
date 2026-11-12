import Markov.PaperQuadrilateralFrontierExact
import Markov.PaperQuadrilateralLocalFiniteness
import Markov.QuadrilateralBoundaryExact

/-! Actual closed-cell adjacency near a literal original side point.
Exact returns identify the only two cells through the point; proved local
finiteness and closedness then exclude all other cells in an actual open
neighborhood. No crossing signs or normal form are assumed. -/

noncomputable section
open Set Topology
open scoped MatrixGroups
namespace Markov

/-- Distinct original sides are disjoint inside the actual upper half-plane;
their ideal common vertices are not points of this space. -/
theorem paperQuadrilateralGeodesicSides_disjoint (i j : Fin 4) (hne : i ≠ j) :
    Disjoint (paperQuadrilateralGeodesicSide i) (paperQuadrilateralGeodesicSide j) := by
  apply Set.disjoint_left.mpr
  intro z hi hj
  have hy := sq_pos_of_pos z.im_pos
  fin_cases i <;> fin_cases j
  all_goals
    dsimp [paperQuadrilateralGeodesicSide, paperRightVerticalSide,
      paperLeftVerticalSide, paperLeftSemicircleSide, paperRightSemicircleSide] at hi hj
    first | exact hne rfl | nlinarith only [hi, hj, hy]

private theorem adjacency_side_unique (i j : Fin 4) (z : UpperHalfPlane)
    (hi : z ∈ paperQuadrilateralGeodesicSide i)
    (hj : z ∈ paperQuadrilateralGeodesicSide j) : i = j := by
  by_contra hne
  exact (Set.disjoint_left.mp (paperQuadrilateralGeodesicSides_disjoint i j hne)) hi hj

/-- The literal neighboring deck cell across each original side, retaining
actual matrices and their actual subgroup membership. Side order is right
vertical, left vertical, left semicircle, right semicircle. -/
def paperQuadrilateralSideNeighbor (k : Fin 4) : modularTraceSubgroup :=
  ⟨paperQuadrilateralSideReturnWordAt (![2, 4, 1, 3] k),
    paperQuadrilateralSideReturnWordAt_mem (![2, 4, 1, 3] k)⟩

private theorem adjacency_neighbor_inv_mem
    (k : Fin 4) (z : UpperHalfPlane) (hz : z ∈ paperQuadrilateralGeodesicSide k) :
    (paperQuadrilateralSideNeighbor k)⁻¹ • z ∈ paperIdealQuadrilateral := by
  have hzQ := paperQuadrilateralGeodesicSide_subset k hz
  fin_cases k
  · change (paperGeneratorASL⁻¹)⁻¹ • z ∈ paperIdealQuadrilateral
    rw [inv_inv]
    exact (paperGeneratorA_quadrilateral_return_iff z hzQ).mpr hz
  · change (paperGeneratorBSL⁻¹)⁻¹ • z ∈ paperIdealQuadrilateral
    rw [inv_inv]
    exact (paperGeneratorB_quadrilateral_return_iff z hzQ).mpr hz
  · change paperGeneratorASL⁻¹ • z ∈ paperIdealQuadrilateral
    exact (paperGeneratorA_inv_quadrilateral_return_iff z hzQ).mpr hz
  · change paperGeneratorBSL⁻¹ • z ∈ paperIdealQuadrilateral
    exact (paperGeneratorB_inv_quadrilateral_return_iff z hzQ).mpr hz

/-- Exactly the original and its actual paired neighboring cell contain an
actual original-side point. The closed return classification is decisive. -/
theorem paperQuadrilateral_side_point_cell_iff
    (k : Fin 4) (z : UpperHalfPlane) (hz : z ∈ paperQuadrilateralGeodesicSide k)
    (δ : modularTraceSubgroup) :
    z ∈ (fun w : UpperHalfPlane => δ • w) '' paperIdealQuadrilateral ↔
      δ = 1 ∨ δ = paperQuadrilateralSideNeighbor k := by
  constructor
  · rintro ⟨w, hw, heq⟩
    have hzQ := paperQuadrilateralGeodesicSide_subset k hz
    have hret : δ⁻¹ • z ∈ paperIdealQuadrilateral := by
      rw [← heq, inv_smul_smul]
      exact hw
    obtain ⟨i, hi⟩ := paperIdealQuadrilateral_return_word (δ⁻¹).val (δ⁻¹).property z hzQ hret
    have hiret : paperQuadrilateralSideReturnWordAt i • z ∈ paperIdealQuadrilateral := by
      rw [← hi]
      exact hret
    have hinv : δ⁻¹ = 1 ∨ δ⁻¹ = (paperQuadrilateralSideNeighbor k)⁻¹ := by
      fin_cases i
      · exact Or.inl (Subtype.ext hi)
      · have hs : z ∈ paperQuadrilateralGeodesicSide 0 :=
          (paperGeneratorA_quadrilateral_return_iff z hzQ).mp hiret
        have hk := adjacency_side_unique k 0 z hz hs
        subst k
        right
        apply Subtype.ext
        change (δ⁻¹).val = (paperGeneratorASL⁻¹)⁻¹
        rw [inv_inv]
        exact hi
      · have hs : z ∈ paperQuadrilateralGeodesicSide 2 :=
          (paperGeneratorA_inv_quadrilateral_return_iff z hzQ).mp hiret
        have hk := adjacency_side_unique k 2 z hz hs
        subst k
        right
        apply Subtype.ext
        exact hi
      · have hs : z ∈ paperQuadrilateralGeodesicSide 1 :=
          (paperGeneratorB_quadrilateral_return_iff z hzQ).mp hiret
        have hk := adjacency_side_unique k 1 z hz hs
        subst k
        right
        apply Subtype.ext
        change (δ⁻¹).val = (paperGeneratorBSL⁻¹)⁻¹
        rw [inv_inv]
        exact hi
      · have hs : z ∈ paperQuadrilateralGeodesicSide 3 :=
          (paperGeneratorB_inv_quadrilateral_return_iff z hzQ).mp hiret
        have hk := adjacency_side_unique k 3 z hz hs
        subst k
        right
        apply Subtype.ext
        exact hi
    rcases hinv with hi | hi
    · exact Or.inl (inv_eq_one.mp hi)
    · exact Or.inr (inv_injective hi)
  · rintro (rfl | rfl)
    · exact ⟨z, paperQuadrilateralGeodesicSide_subset k hz, one_smul _ _⟩
    · exact ⟨(paperQuadrilateralSideNeighbor k)⁻¹ • z,
        adjacency_neighbor_inv_mem k z hz, smul_inv_smul _ _⟩

/-- There is an actual open neighborhood of each original side point in which
only its two actual closed adjacent cells can occur. This is derived from
finite closed-cell incidence, not assumed as an adjacency field. -/
theorem paperQuadrilateral_side_local_two_cells
    (k : Fin 4) (z : UpperHalfPlane) (hz : z ∈ paperQuadrilateralGeodesicSide k) :
    ∃ U : Set UpperHalfPlane, IsOpen U ∧ z ∈ U ∧
      ∀ w ∈ U, ∀ δ : modularTraceSubgroup,
        w ∈ (fun v : UpperHalfPlane => δ • v) '' paperIdealQuadrilateral →
          δ = 1 ∨ δ = paperQuadrilateralSideNeighbor k := by
  let S : Set modularTraceSubgroup :=
    {δ | ∃ v ∈ paperIdealQuadrilateral, δ • v ∈ Metric.closedBall z 1}
  have hS : S.Finite := paperIdealQuadrilateral_closedBall_finite_cells z 1
  let B := {δ ∈ S | δ ≠ 1 ∧ δ ≠ paperQuadrilateralSideNeighbor k}
  have hB : B.Finite := hS.subset (fun _ h => h.1)
  let V : Set UpperHalfPlane := ⋃ δ ∈ B,
    (fun v : UpperHalfPlane => δ • v) '' paperIdealQuadrilateral
  have hV : IsClosed V := hB.isClosed_biUnion (fun δ _ =>
    (Homeomorph.smul δ).isClosed_image.mpr paperIdealQuadrilateral_isClosed)
  have hzV : z ∉ V := by
    rintro ⟨_, ⟨δ, rfl⟩, _, ⟨hδ, rfl⟩, hcell⟩
    rcases (paperQuadrilateral_side_point_cell_iff k z hz δ).mp hcell with he | he
    · exact hδ.2.1 he
    · exact hδ.2.2 he
  refine ⟨Metric.ball z 1 ∩ Vᶜ, Metric.isOpen_ball.inter hV.isOpen_compl,
    ⟨Metric.mem_ball_self (by norm_num), hzV⟩, ?_⟩
  intro w hw δ hcell
  by_contra hnot
  have hδS : δ ∈ S := by
    obtain ⟨v, hv, hveq⟩ := hcell
    change δ • v = w at hveq
    refine ⟨v, hv, ?_⟩
    rw [hveq]
    exact Metric.ball_subset_closedBall hw.1
  have hδB : δ ∈ B := ⟨hδS, not_or.mp hnot⟩
  exact hw.2 (Set.mem_iUnion.mpr ⟨δ, Set.mem_iUnion.mpr ⟨hδB, hcell⟩⟩)

/-- The same actual neighborhood is covered by the two stated closed cells;
this uses actual quadrilateral quotient coverage, not a planar picture. -/
theorem paperQuadrilateral_side_local_adjacent_cover
    (k : Fin 4) (z : UpperHalfPlane) (hz : z ∈ paperQuadrilateralGeodesicSide k) :
    ∃ U : Set UpperHalfPlane, IsOpen U ∧ z ∈ U ∧
      U ⊆ paperIdealQuadrilateral ∪
        (fun v : UpperHalfPlane => paperQuadrilateralSideNeighbor k • v) ''
          paperIdealQuadrilateral := by
  obtain ⟨U, hU, hzU, hcells⟩ := paperQuadrilateral_side_local_two_cells k z hz
  refine ⟨U, hU, hzU, ?_⟩
  intro w hw
  obtain ⟨v, hv, hproj⟩ := paperIdealQuadrilateral_quotient_coverage (modularTraceQuotientMk w)
  obtain ⟨δ, hδ⟩ := (modularTraceQuotientMk_eq_iff w v).mp hproj.symm
  have hcell : w ∈ (fun x : UpperHalfPlane => δ • x) '' paperIdealQuadrilateral :=
    ⟨v, hv, hδ⟩
  rcases hcells w hw δ hcell with he | he
  · left
    obtain ⟨x, hx, hxw⟩ := hcell
    change δ • x = w at hxw
    rw [he, one_smul] at hxw
    exact hxw ▸ hx
  · right
    simpa only [he] using hcell

end Markov
