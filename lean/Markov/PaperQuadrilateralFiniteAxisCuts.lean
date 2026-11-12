import Markov.HyperbolicAxesSingleIntersection
import Markov.PeriodicAxisLeavesQuadrilateral

/-! Literal original side parametrizations and finite actual cut times for
any closed hyperbolic deck axis. Coincident sides are excluded by the proved
compact-return obstruction; closed-cell local finiteness is genuinely used.
No finite normal-diagram classification or cyclic-word conclusion is assumed. -/

noncomputable section
open Set Topology
namespace Markov

private def paperShiftedVerticalLine (c t : ℝ) : UpperHalfPlane :=
  c +ᵥ hyperbolicVerticalAxis t

private theorem paperShiftedVerticalLine_isometry (c : ℝ) :
    Isometry (paperShiftedVerticalLine c) :=
  (UpperHalfPlane.isometry_real_vadd c).comp hyperbolicVerticalAxis_isometry

private theorem paperShiftedVerticalLine_range (c : ℝ) :
    range (paperShiftedVerticalLine c) = {z : UpperHalfPlane | z.re = c} := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    simp [paperShiftedVerticalLine, hyperbolicVerticalAxis]
  · intro hz
    refine ⟨Real.log z.im, ?_⟩
    apply UpperHalfPlane.ext_re_im
    · simpa only [paperShiftedVerticalLine, UpperHalfPlane.vadd_re,
        hyperbolicVerticalAxis, UpperHalfPlane.mk_re, add_zero] using hz.symm
    · simpa only [paperShiftedVerticalLine, UpperHalfPlane.vadd_im,
        hyperbolicVerticalAxis, UpperHalfPlane.mk_im] using Real.exp_log z.im_pos

/-- The four literal original closed side subsets, with original A/B labels. -/
def paperQuadrilateralGeodesicSide (k : Fin 4) : Set UpperHalfPlane :=
  ![paperRightVerticalSide, paperLeftVerticalSide,
    paperLeftSemicircleSide, paperRightSemicircleSide] k

/-- Actual unit-speed parametrizations of the original four complete sides.
The semicircles use the already proved literal original A/B side maps. -/
def paperQuadrilateralGeodesicSideLine (k : Fin 4) : ℝ → UpperHalfPlane :=
  ![paperShiftedVerticalLine 1, paperShiftedVerticalLine (-1),
    (fun z : UpperHalfPlane => paperGeneratorASL • z) ∘ paperShiftedVerticalLine 1,
    (fun z : UpperHalfPlane => paperGeneratorBSL • z) ∘ paperShiftedVerticalLine (-1)] k

theorem paperQuadrilateralGeodesicSideLine_isometry (k : Fin 4) :
    Isometry (paperQuadrilateralGeodesicSideLine k) := by
  fin_cases k
  · exact paperShiftedVerticalLine_isometry 1
  · exact paperShiftedVerticalLine_isometry (-1)
  · exact (modularInteger_isometry paperGeneratorASL).comp (paperShiftedVerticalLine_isometry 1)
  · exact (modularInteger_isometry paperGeneratorBSL).comp (paperShiftedVerticalLine_isometry (-1))

theorem paperQuadrilateralGeodesicSideLine_range (k : Fin 4) :
    range (paperQuadrilateralGeodesicSideLine k) = paperQuadrilateralGeodesicSide k := by
  fin_cases k
  · exact paperShiftedVerticalLine_range 1
  · exact paperShiftedVerticalLine_range (-1)
  · change range ((fun z : UpperHalfPlane => paperGeneratorASL • z) ∘
      paperShiftedVerticalLine 1) = paperLeftSemicircleSide
    rw [Set.range_comp (fun z : UpperHalfPlane => paperGeneratorASL • z)
      (paperShiftedVerticalLine 1), paperShiftedVerticalLine_range]
    exact paperGeneratorA_image_side
  · change range ((fun z : UpperHalfPlane => paperGeneratorBSL • z) ∘
      paperShiftedVerticalLine (-1)) = paperRightSemicircleSide
    rw [Set.range_comp (fun z : UpperHalfPlane => paperGeneratorBSL • z)
      (paperShiftedVerticalLine (-1)), paperShiftedVerticalLine_range]
    exact paperGeneratorB_image_side

theorem paperQuadrilateralGeodesicSide_subset (k : Fin 4) :
    paperQuadrilateralGeodesicSide k ⊆ paperIdealQuadrilateral := by
  fin_cases k
  · exact paperRightVerticalSide_subset_quadrilateral
  · exact paperLeftVerticalSide_subset_quadrilateral
  · exact paperLeftSemicircleSide_subset_quadrilateral
  · exact paperRightSemicircleSide_subset_quadrilateral

theorem paperQuadrilateralGeodesicSideLine_translate_range
    (δ : modularTraceSubgroup) (k : Fin 4) :
    range (fun t => δ • paperQuadrilateralGeodesicSideLine k t) =
      (fun z : UpperHalfPlane => δ • z) '' paperQuadrilateralGeodesicSide k := by
  rw [← paperQuadrilateralGeodesicSideLine_range k, ← Set.range_comp']

/-- Actual periodic axes never coincide with an actual translated ideal edge.
The whole edge lies in that full closed cell, whose compact return forbids it. -/
theorem modularHyperbolicAxis_ne_translated_paper_side_range
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (δ : modularTraceSubgroup) (k : Fin 4) :
    range (fun t => δ • paperQuadrilateralGeodesicSideLine k t) ≠
      range (modularHyperbolicAxis g hg) := by
  intro heq
  apply modularHyperbolicAxis_not_contained_quadrilateral_translate g hg δ
  rw [← heq, paperQuadrilateralGeodesicSideLine_translate_range]
  exact Set.image_mono (paperQuadrilateralGeodesicSide_subset k)

/-- A fixed translated original edge can be met at most once by any actual
hyperbolic deck axis. No transversality assumption or canonical-word input. -/
theorem modularHyperbolicAxis_paper_side_cut_subsingleton
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (δ : modularTraceSubgroup) (k : Fin 4) :
    {t : ℝ | modularHyperbolicAxis g hg t ∈
      (fun z : UpperHalfPlane => δ • z) '' paperQuadrilateralGeodesicSide k}.Subsingleton := by
  have hp := upperHalfPlane_distinct_isometric_lines_intersection_subsingleton
    (modularHyperbolicAxis g hg) (fun t => δ • paperQuadrilateralGeodesicSideLine k t)
    (modularHyperbolicAxis_isometry g hg)
    ((modularTraceSubgroup_isometry δ).comp (paperQuadrilateralGeodesicSideLine_isometry k))
    (modularHyperbolicAxis_ne_translated_paper_side_range g hg δ k)
  intro t ht u hu
  apply (modularHyperbolicAxis_isometry g hg).injective
  apply hp
  · exact ⟨by rwa [paperQuadrilateralGeodesicSideLine_translate_range], ⟨t, rfl⟩⟩
  · exact ⟨by rwa [paperQuadrilateralGeodesicSideLine_translate_range], ⟨u, rfl⟩⟩

/-- Any compact actual hyperbolic deck-axis segment has finitely many literal
original-side cut parameters, including every deck label and all four sides.
The finite cell set and the noncoincidence proof discharge those two inputs. -/
theorem modularHyperbolicAxis_finite_paper_side_cuts
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a b : ℝ) :
    {t : ℝ | t ∈ Icc a b ∧ ∃ δ : modularTraceSubgroup, ∃ k : Fin 4,
      modularHyperbolicAxis g hg t ∈
        (fun z : UpperHalfPlane => δ • z) '' paperQuadrilateralGeodesicSide k}.Finite := by
  let C : Set modularTraceSubgroup := {δ | ∃ t ∈ Icc a b,
    ∃ z ∈ paperIdealQuadrilateral, δ • z = modularHyperbolicAxis g hg t}
  have hC : C.Finite := paperIdealQuadrilateral_axis_segment_finite_cells g hg a b
  have hf : (⋃ δ ∈ C, ⋃ k : Fin 4,
      {t : ℝ | modularHyperbolicAxis g hg t ∈
        (fun z : UpperHalfPlane => δ • z) '' paperQuadrilateralGeodesicSide k}).Finite := by
    apply hC.biUnion
    intro δ _
    exact Set.finite_iUnion (fun k =>
      (modularHyperbolicAxis_paper_side_cut_subsingleton g hg δ k).finite)
  apply hf.subset
  rintro t ⟨ht, δ, k, z, hz, heq⟩
  refine mem_iUnion₂.mpr ⟨δ, ?_, mem_iUnion.mpr ⟨k, z, hz, heq⟩⟩
  exact ⟨t, ht, z, paperQuadrilateralGeodesicSide_subset k hz, heq⟩

end Markov
