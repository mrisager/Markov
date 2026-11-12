import Markov.PaperAxisNormalArcNoncrossing
import Markov.PaperAxisWrapGapDisjoint
import Markov.DiskChordEndpointDistinct

/-! Actual wrap-versus-internal endpoint-chord noncrossing for the complete
proper-arc family. The wrap is the genuinely joined Q-valued path. Any needed
cross-endpoint distinctness follows from the proposed transverse chord crossing
itself, not from an additional endpoint-distinctness or classification premise. -/

noncomputable section
open Set Topology
namespace Markov

/-- The actual complex disk coordinate of the genuinely joined wrap arc. -/
def paperAxisPeriodWrapDiskArc (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) : unitInterval → ℂ :=
  paperQuadrilateralDiskCoordinate ∘ paperAxisPeriodWrapSubarc g hg a ha

/-- The actual wrap arc and each actual internal normal gap have no transverse
interior endpoint-chord crossing. All proper-arc and open-disjointness inputs
are proved from the actual geometry; cross-endpoint distinctness is forced by
nonzero chord determinant and the proposed interior chord intersection. -/
theorem paperAxisPeriodWrapDiskArc_no_transverse_chord_crossing
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card-1))
    (hfirst : 0 < i.val) (hlast : i.val+2 < (paperAxisPeriodCutPoints g hg a).card)
    (hd : (paperAxisPeriodWrapDiskArc g hg a ha 1-paperAxisPeriodWrapDiskArc g hg a ha 0).re *
        (paperAxisPeriodGapDiskArc g hg a i 1-paperAxisPeriodGapDiskArc g hg a i 0).im -
      (paperAxisPeriodWrapDiskArc g hg a ha 1-paperAxisPeriodWrapDiskArc g hg a ha 0).im *
        (paperAxisPeriodGapDiskArc g hg a i 1-paperAxisPeriodGapDiskArc g hg a i 0).re ≠ 0)
    (u v : unitInterval) (hu0 : 0 < (u:ℝ)) (hu1 : (u:ℝ) < 1)
    (hv0 : 0 < (v:ℝ)) (hv1 : (v:ℝ) < 1)
    (hchord : diskArcChord (paperAxisPeriodWrapDiskArc g hg a ha) u =
      diskArcChord (paperAxisPeriodGapDiskArc g hg a i) v) : False := by
  have hends := diskArcChord_cross_endpoints_ne_of_transverse_interior_intersection
    (paperAxisPeriodWrapDiskArc g hg a ha) (paperAxisPeriodGapDiskArc g hg a i)
    hd u v hu0 hu1 hchord
  obtain ⟨kw, lw, _, hwL, hwR, _, _⟩ := paperAxisPeriodWrapSubarc_endpoint_sides g hg a ha
  obtain ⟨ki, li, _, hiL, hiR, _, _⟩ := paperAxisPeriodGapSubarc_internal_endpoint_sides g hg a i hfirst hlast
  exact paperQuadrilateral_disjoint_proper_arcs_no_transverse_chord_crossing
    (paperAxisPeriodWrapSubarc g hg a ha) (paperAxisPeriodGapSubarc g hg a i)
    (paperAxisPeriodWrapSubarc g hg a ha).continuous (paperAxisPeriodGapSubarc g hg a i).continuous
    (paperQuadrilateralGeodesicSide_subset_frontier kw hwL)
    (paperQuadrilateralGeodesicSide_subset_frontier lw hwR)
    (paperQuadrilateralGeodesicSide_subset_frontier ki hiL)
    (paperQuadrilateralGeodesicSide_subset_frontier li hiR)
    (fun h => (zero_ne_one : (0:unitInterval) ≠ 1)
      ((paperAxisPeriodWrapSubarc_isClosedEmbedding g hg a ha).injective h))
    (fun h => (zero_ne_one : (0:unitInterval) ≠ 1) (paperAxisPeriodGapSubarc_injective g hg a i h))
    (paperAxisPeriodWrapSubarc_strict g hg a ha) (paperAxisPeriodGapSubarc_strict g hg a i)
    (fun s t hs ht heq => hends s t hs ht (congrArg paperQuadrilateralDiskCoordinate heq))
    (paperAxisPeriodWrapSubarc_internalGap_interiors_disjoint g hg a ha hproject i hfirst hlast)
    hd u v hu0 hu1 hv0 hv1 hchord

end Markov
