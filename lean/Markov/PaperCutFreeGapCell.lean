import Markov.PaperStrictCellReturns
import Mathlib.Topology.Order.IntermediateValue

/-! A cut-free actual continuous parameter gap lies in one actual translated
strict original cell, with its endpoints in that same closed cell. Cell-label
uniqueness follows from the checked strict representative theorem and actual
free action. No normal-form, adjacency, or sign-change hypothesis is used. -/

noncomputable section
open Set Topology
namespace Markov

/-- A point in a translated strict cell has a unique closed-cell deck label.
Both the strict representative and the deck label are forced by actual
quotient uniqueness and cancellation of the actual free action. -/
theorem paperStrictCell_label_unique (δ ε : modularTraceSubgroup)
    (x : UpperHalfPlane)
    (hδ : x ∈ (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateralStrictRegion)
    (hε : x ∈ (fun z : UpperHalfPlane => ε • z) '' paperIdealQuadrilateral) : δ = ε := by
  obtain ⟨z, hz, hzx⟩ := hδ
  obtain ⟨w, hw, hwx⟩ := hε
  have hproj : modularTraceQuotientMk z = modularTraceQuotientMk w := by
    calc
      _ = modularTraceQuotientMk (δ • z) := (modularTraceQuotientMk_smul δ z).symm
      _ = modularTraceQuotientMk (ε • w) := congrArg modularTraceQuotientMk (hzx.trans hwx.symm)
      _ = _ := modularTraceQuotientMk_smul ε w
  have hzw := paperIdealQuadrilateralStrictRegion_quotient_unique z w hz hw hproj
  rw [← hzw] at hwx
  exact IsCancelSMul.right_cancel δ ε z (hzx.trans hwx.symm)

/-- Actual quotient coverage and avoidance of all four translated literal
sides give exactly one translated strict-cell label. -/
theorem paperStrictCell_existsUnique_of_off_sides (x : UpperHalfPlane)
    (hoff : ∀ δ : modularTraceSubgroup, ∀ k : Fin 4,
      x ∉ (fun z : UpperHalfPlane => δ • z) '' paperQuadrilateralGeodesicSide k) :
    ∃! δ : modularTraceSubgroup,
      x ∈ (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateralStrictRegion := by
  obtain ⟨z, hz, hproj⟩ := paperIdealQuadrilateral_quotient_coverage (modularTraceQuotientMk x)
  obtain ⟨δ, hδ⟩ := (modularTraceQuotientMk_eq_iff x z).mp hproj.symm
  have hside (k : Fin 4) : z ∉ paperQuadrilateralGeodesicSide k := by
    intro hk
    exact hoff δ k ⟨z, hk, hδ⟩
  have h0 : z.re ≠ 1 := hside 0
  have h1 : z.re ≠ -1 := hside 1
  have h2 : z.re ^ 2 + z.re + z.im ^ 2 ≠ 0 := hside 2
  have h3 : z.re ^ 2 - z.re + z.im ^ 2 ≠ 0 := hside 3
  obtain ⟨hl, hr, hleft, hright⟩ := hz
  have hstrict : z ∈ paperIdealQuadrilateralStrictRegion :=
    ⟨lt_of_le_of_ne hl h1.symm, lt_of_le_of_ne hr h0,
      lt_of_le_of_ne hleft h2.symm, lt_of_le_of_ne hright h3.symm⟩
  refine ⟨δ, ⟨z, hstrict, hδ⟩, ?_⟩
  intro ε hε
  exact paperStrictCell_label_unique ε δ x hε
    ⟨z, paperIdealQuadrilateralStrictRegion_subset hstrict, hδ⟩

/-- The actual point and deck witnesses for the unique strict-cell label,
with the original strict point and action equality displayed explicitly. -/
theorem paperStrictCell_exists_of_off_sides (x : UpperHalfPlane)
    (hoff : ∀ δ : modularTraceSubgroup, ∀ k : Fin 4,
      x ∉ (fun z : UpperHalfPlane => δ • z) '' paperQuadrilateralGeodesicSide k) :
    ∃ δ : modularTraceSubgroup, ∃ z ∈ paperIdealQuadrilateralStrictRegion, δ • z = x := by
  obtain ⟨δ, ⟨z, hz, heq⟩, _⟩ := paperStrictCell_existsUnique_of_off_sides x hoff
  exact ⟨δ, z, hz, heq⟩

/-- A continuous curve avoiding every translated original side throughout an
open parameter gap stays in one strict cell. Its two endpoints belong to the
same closed cell. The open strict-cell labels are disjoint by actual label
uniqueness, so connectedness makes the label constant. -/
theorem continuous_paper_cutFree_gap_cell
    (F : ℝ → UpperHalfPlane) (hF : Continuous F) (a b : ℝ) (hab : a < b)
    (hoff : ∀ t ∈ Ioo a b, ∀ δ : modularTraceSubgroup, ∀ k : Fin 4,
      F t ∉ (fun z : UpperHalfPlane => δ • z) '' paperQuadrilateralGeodesicSide k) :
    ∃ δ : modularTraceSubgroup,
      (∀ t ∈ Ioo a b,
        F t ∈ (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateralStrictRegion) ∧
      ∀ t ∈ Icc a b,
        F t ∈ (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral := by
  classical
  obtain ⟨t₀, ht₀⟩ := nonempty_Ioo.mpr hab
  obtain ⟨δ, hδ, _⟩ := paperStrictCell_existsUnique_of_off_sides (F t₀) (hoff t₀ ht₀)
  let C (ε : modularTraceSubgroup) : Set UpperHalfPlane :=
    (fun z : UpperHalfPlane => ε • z) '' paperIdealQuadrilateralStrictRegion
  let V : Set UpperHalfPlane := ⋃ ε : {ε : modularTraceSubgroup // ε ≠ δ}, C ε.val
  have hCopen (ε : modularTraceSubgroup) : IsOpen (C ε) :=
    (Homeomorph.smul ε).isOpenMap _ paperIdealQuadrilateralStrictRegion_isOpen
  have hVopen : IsOpen V := isOpen_iUnion (fun ε => hCopen ε.val)
  have hdisj : Disjoint (C δ) V := by
    apply disjoint_left.mpr
    intro x hxδ hxV
    obtain ⟨ε, hxε⟩ := mem_iUnion.mp hxV
    apply ε.property
    exact paperStrictCell_label_unique ε.val δ x hxε
      (Set.image_mono paperIdealQuadrilateralStrictRegion_subset hxδ)
  have hcover : F '' Ioo a b ⊆ C δ ∪ V := by
    rintro x ⟨t, ht, rfl⟩
    obtain ⟨ε, hε, _⟩ := paperStrictCell_existsUnique_of_off_sides (F t) (hoff t ht)
    by_cases heq : ε = δ
    · exact Or.inl (heq ▸ hε)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨ε, heq⟩, hε⟩)
  have hconn : IsPreconnected (F '' Ioo a b) := isPreconnected_Ioo.image F hF.continuousOn
  have hinter : ∀ t ∈ Ioo a b, F t ∈ C δ := by
    rcases hconn.subset_or_subset (hCopen δ) hVopen hdisj hcover with hin | hout
    · exact fun t ht => hin ⟨t, ht, rfl⟩
    · exact (disjoint_left.mp hdisj hδ (hout ⟨t₀, ht₀, rfl⟩)).elim
  have hQclosed : IsClosed ((fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral) :=
    (Homeomorph.smul δ).isClosedMap _ paperIdealQuadrilateral_isClosed
  have hclosed : IsClosed (F ⁻¹' ((fun z : UpperHalfPlane => δ • z) ''
      paperIdealQuadrilateral)) := hQclosed.preimage hF
  have hsub : Ioo a b ⊆ F ⁻¹' ((fun z : UpperHalfPlane => δ • z) ''
      paperIdealQuadrilateral) := by
    intro t ht
    exact Set.image_mono paperIdealQuadrilateralStrictRegion_subset (hinter t ht)
  have hclosure := closure_minimal hsub hclosed
  rw [closure_Ioo hab.ne] at hclosure
  exact ⟨δ, hinter, fun t ht => hclosure ht⟩

end Markov
