import Markov.PaperQuadrilateralQuotient
import Markov.ModularClosedGeodesic

/-! Actual local finiteness of all closed ideal-quadrilateral translates.
The quadrilateral itself is noncompact. Its proved proper projection and the
actual two-compact proper-discontinuity theorem give compact return finiteness.
All closed edges and corners are retained. No normal-arc classifier is assumed. -/

noncomputable section
open Set Topology
namespace Markov

/-- The actual closed quadrilateral is compact above the orbit projection of
any actual compact set upstairs. This uses its proved proper restriction. -/
theorem paperIdealQuadrilateral_compact_over_compact_image
    (K : Set UpperHalfPlane) (hK : IsCompact K) :
    IsCompact {z : UpperHalfPlane | z ∈ paperIdealQuadrilateral ∧
      modularTraceQuotientMk z ∈ modularTraceQuotientMk '' K} := by
  have hc := (paperQuadrilateralQuotientMap_isCompact_preimage
    (modularTraceQuotientMk '' K) (hK.image modularTraceQuotientMk_continuous)).image
      continuous_subtype_val
  convert hc using 1
  ext z
  constructor
  · rintro ⟨hz, hp⟩
    exact ⟨⟨z, hz⟩, hp, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩

/-- Only finitely many actual deck translates of the full CLOSED original
quadrilateral meet a given compact subset of the hyperbolic plane. -/
theorem paperIdealQuadrilateral_finite_translates_meeting_compact
    (K : Set UpperHalfPlane) (hK : IsCompact K) :
    {g : modularTraceSubgroup | ∃ z ∈ paperIdealQuadrilateral, g • z ∈ K}.Finite := by
  let R : Set UpperHalfPlane := {z | z ∈ paperIdealQuadrilateral ∧
    modularTraceQuotientMk z ∈ modularTraceQuotientMk '' K}
  have hR : IsCompact R := paperIdealQuadrilateral_compact_over_compact_image K hK
  have hf : {g : modularTraceSubgroup | ((g • ·) '' R ∩ K).Nonempty}.Finite :=
    finite_disjoint_inter_image hR hK
  apply hf.subset
  rintro g ⟨z, hz, hgz⟩
  refine ⟨g • z, ⟨z, ⟨hz, ?_⟩, rfl⟩, hgz⟩
  exact ⟨g • z, hgz, modularTraceQuotientMk_smul g z⟩

/-- Actual compact curve segments meet only finitely many closed original
quadrilateral translates. No transversality or boundary-choice premise is used. -/
theorem paperIdealQuadrilateral_curve_segment_finite_cells
    (f : C(ℝ, UpperHalfPlane)) (a b : ℝ) :
    {g : modularTraceSubgroup | ∃ t ∈ Icc a b,
      ∃ z ∈ paperIdealQuadrilateral, g • z = f t}.Finite := by
  apply (paperIdealQuadrilateral_finite_translates_meeting_compact
    (f '' Icc a b) (isCompact_Icc.image f.continuous)).subset
  rintro g ⟨t, ht, z, hz, heq⟩
  exact ⟨z, hz, t, ht, heq.symm⟩

/-- The actual invariant axis segment of any actual hyperbolic deck element
has finite closed-cell incidence, without a canonical-word or simplicity input. -/
theorem paperIdealQuadrilateral_axis_segment_finite_cells
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a b : ℝ) :
    {h : modularTraceSubgroup | ∃ t ∈ Icc a b,
      ∃ z ∈ paperIdealQuadrilateral, h • z = modularHyperbolicAxis g hg t}.Finite :=
  paperIdealQuadrilateral_curve_segment_finite_cells
    ⟨modularHyperbolicAxis g hg, (modularHyperbolicAxis_isometry g hg).continuous⟩ a b

/-- A literal compact ball gives actual local finiteness near every point,
including all closed cell edges and corners. -/
theorem paperIdealQuadrilateral_closedBall_finite_cells
    (z : UpperHalfPlane) (R : ℝ) :
    {g : modularTraceSubgroup | ∃ w ∈ paperIdealQuadrilateral,
      g • w ∈ Metric.closedBall z R}.Finite :=
  paperIdealQuadrilateral_finite_translates_meeting_compact _ (isCompact_closedBall z R)

end Markov
