import Markov.PaperAxisAllCornersNearest
import Markov.PaperAxisExtremeEndpointSet
import Markov.PaperAxisProperSixArcCounts

/-! Genuine ARC closure of actual side extrema from the proved all-four
nearest-corner geometry. Positive actual corner counts construct all four
actual corner witnesses using the proved count balance. No ARC-closure,
peripheral-layer, matching or simple-class classification field is supplied. -/

noncomputable section
open Set
namespace Markov

private theorem extreme_boundary_formula
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (t : paperAxisProperEndpointTag g hg a) :
    paperAxisProperEndpointBoundaryCoordinate g hg a ha t =
      if paperAxisProperEndpointSide g hg a ha t = 1 ∨
          paperAxisProperEndpointSide g hg a ha t = 2 then
        -paperAxisProperEndpointCoordinate g hg a ha t
      else paperAxisProperEndpointCoordinate g hg a ha t := by
  unfold paperAxisProperEndpointBoundaryCoordinate paperAxisProperEndpointCoordinate
  generalize paperAxisProperEndpointSide g hg a ha t = k
  fin_cases k <;> simp [paperQuadrilateralBoundarySideCoordinate]

private theorem extreme_mem_iff_boundary
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (t : paperAxisProperEndpointTag g hg a) :
    t ∈ paperAxisExtremeEndpointSet g hg a ha ↔
      (∀ u, paperAxisProperEndpointSide g hg a ha u = paperAxisProperEndpointSide g hg a ha t →
        paperAxisProperEndpointBoundaryCoordinate g hg a ha t ≤
          paperAxisProperEndpointBoundaryCoordinate g hg a ha u) ∨
      (∀ u, paperAxisProperEndpointSide g hg a ha u = paperAxisProperEndpointSide g hg a ha t →
        paperAxisProperEndpointBoundaryCoordinate g hg a ha u ≤
          paperAxisProperEndpointBoundaryCoordinate g hg a ha t) := by
  have hform (u : paperAxisProperEndpointTag g hg a)
      (hu : paperAxisProperEndpointSide g hg a ha u = paperAxisProperEndpointSide g hg a ha t) :
      paperAxisProperEndpointBoundaryCoordinate g hg a ha u =
        if paperAxisProperEndpointSide g hg a ha t = 1 ∨
            paperAxisProperEndpointSide g hg a ha t = 2 then
          -paperAxisProperEndpointCoordinate g hg a ha u
        else paperAxisProperEndpointCoordinate g hg a ha u := by
    rw [extreme_boundary_formula, hu]
  by_cases hsign : paperAxisProperEndpointSide g hg a ha t = 1 ∨
      paperAxisProperEndpointSide g hg a ha t = 2
  · constructor
    · rintro (hmin | hmax)
      · refine Or.inr ?_
        intro u hu
        rw [hform u hu, extreme_boundary_formula, if_pos hsign, if_pos hsign]
        exact neg_le_neg (hmin u hu)
      · refine Or.inl ?_
        intro u hu
        rw [extreme_boundary_formula, hform u hu, if_pos hsign, if_pos hsign]
        exact neg_le_neg (hmax u hu)
    · rintro (hmin | hmax)
      · refine Or.inr ?_
        intro u hu
        have hh := hmin u hu
        rw [extreme_boundary_formula, hform u hu, if_pos hsign, if_pos hsign] at hh
        exact neg_le_neg_iff.mp hh
      · refine Or.inl ?_
        intro u hu
        have hh := hmax u hu
        rw [hform u hu, extreme_boundary_formula, if_pos hsign, if_pos hsign] at hh
        exact neg_le_neg_iff.mp hh
  · constructor
    · rintro (hmin | hmax)
      · refine Or.inl ?_
        intro u hu
        rw [extreme_boundary_formula, hform u hu, if_neg hsign, if_neg hsign]
        exact hmin u hu
      · refine Or.inr ?_
        intro u hu
        rw [hform u hu, extreme_boundary_formula, if_neg hsign, if_neg hsign]
        exact hmax u hu
    · rintro (hmin | hmax)
      · refine Or.inl ?_
        intro u hu
        have hh := hmin u hu
        rwa [extreme_boundary_formula, hform u hu, if_neg hsign, if_neg hsign] at hh
      · refine Or.inr ?_
        intro u hu
        have hh := hmax u hu
        rwa [hform u hu, extreme_boundary_formula, if_neg hsign, if_neg hsign] at hh

private theorem extreme_boundary_min_max_exists
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4)
    (hside : ∃ t : paperAxisProperEndpointTag g hg a,
      paperAxisProperEndpointSide g hg a ha t = k) :
    ∃ t u : paperAxisProperEndpointTag g hg a,
      paperAxisProperEndpointSide g hg a ha t = k ∧
      paperAxisProperEndpointSide g hg a ha u = k ∧
      (∀ v, paperAxisProperEndpointSide g hg a ha v = k →
        paperAxisProperEndpointBoundaryCoordinate g hg a ha t ≤
          paperAxisProperEndpointBoundaryCoordinate g hg a ha v) ∧
      (∀ v, paperAxisProperEndpointSide g hg a ha v = k →
        paperAxisProperEndpointBoundaryCoordinate g hg a ha v ≤
          paperAxisProperEndpointBoundaryCoordinate g hg a ha u) := by
  classical
  let T := paperAxisProperEndpointSideTags g hg a ha k
  have hmem (v : paperAxisProperEndpointTag g hg a) :
      v ∈ T ↔ paperAxisProperEndpointSide g hg a ha v = k := by
    simp only [T, paperAxisProperEndpointSideTags, Finset.mem_filter,
      Finset.mem_univ, true_and]
  obtain ⟨v, hv⟩ := hside
  have hT : T.Nonempty := ⟨v, (hmem v).mpr hv⟩
  obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image T
    (paperAxisProperEndpointBoundaryCoordinate g hg a ha) hT
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image T
    (paperAxisProperEndpointBoundaryCoordinate g hg a ha) hT
  exact ⟨t, u, (hmem t).mp ht, (hmem u).mp hu,
    fun w hw => hmin w ((hmem w).mpr hw),
    fun w hw => hmax w ((hmem w).mpr hw)⟩

/-- Actual nearest-corner geometry makes the actual side-extrema set ARC
closed whenever every literal corner has an actual family arc. The input
describes genuine arcs; ARC closure itself is the proved conclusion. -/
theorem paperAxisExtremeEndpointSet_arc_closed_of_corner_arcs
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (hcorner : ∀ k : Fin 4, ∃ s : paperAxisProperEndpointTag g hg a,
      paperAxisProperEndpointSide g hg a ha s = k ∧
        paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a s) =
          paperQuadrilateralNextSide k) :
    ∀ t ∈ paperAxisExtremeEndpointSet g hg a ha,
      paperAxisProperArcEndpointPair g hg a t ∈ paperAxisExtremeEndpointSet g hg a ha := by
  have hside (k : Fin 4) : ∃ s : paperAxisProperEndpointTag g hg a,
      paperAxisProperEndpointSide g hg a ha s = k := by
    obtain ⟨s, hs, _⟩ := hcorner k
    exact ⟨s, hs⟩
  intro t ht
  rcases (extreme_mem_iff_boundary g hg a ha t).mp ht with hmin | hmax
  · let k := paperQuadrilateralNextSide.symm (paperAxisProperEndpointSide g hg a ha t)
    have hk : paperQuadrilateralNextSide k = paperAxisProperEndpointSide g hg a ha t :=
      paperQuadrilateralNextSide.apply_symm_apply _
    obtain ⟨u, v, _, hv, _, hvmax⟩ :=
      extreme_boundary_min_max_exists g hg a ha k (hside k)
    have hp := paperAxisCorner_extrema_arc_paired g hg a ha hproject k v t hv hk.symm
      hvmax (fun w hw => hmin w (hw.trans hk)) (hcorner k)
    have hvS : v ∈ paperAxisExtremeEndpointSet g hg a ha :=
      (extreme_mem_iff_boundary g hg a ha v).mpr
        (Or.inr (fun w hw => hvmax w (hw.trans hv)))
    have hp' : paperAxisProperArcEndpointPair g hg a t = v := by
      rw [← hp, paperAxisProperArcEndpointPair_involutive]
    rwa [hp']
  · let k := paperAxisProperEndpointSide g hg a ha t
    obtain ⟨u, v, hu, _, humin, _⟩ :=
      extreme_boundary_min_max_exists g hg a ha (paperQuadrilateralNextSide k)
        (hside (paperQuadrilateralNextSide k))
    have hp := paperAxisCorner_extrema_arc_paired g hg a ha hproject k t u rfl hu
      hmax humin (hcorner k)
    have huS : u ∈ paperAxisExtremeEndpointSet g hg a ha :=
      (extreme_mem_iff_boundary g hg a ha u).mpr
        (Or.inl (fun w hw => humin w (hw.trans hu)))
    rwa [hp]

/-- Both actual pairing closures and genuine one-component connectedness
force every actual endpoint to be extremal, under actual corner-arc existence. -/
theorem paperAxisExtremeEndpointSet_eq_univ_of_corner_arcs
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (hcorner : ∀ k : Fin 4, ∃ s : paperAxisProperEndpointTag g hg a,
      paperAxisProperEndpointSide g hg a ha s = k ∧
        paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a s) =
          paperQuadrilateralNextSide k) :
    paperAxisExtremeEndpointSet g hg a ha = Set.univ :=
  paperAxisExtremeEndpointSet_eq_univ_of_arc_closed g hg a ha hproject
    (paperAxisExtremeEndpointSet_arc_closed_of_corner_arcs g hg a ha hproject hcorner)

/-- Positive actual 01 and 12 counts construct an actual oriented corner arc
at every corner. The actual balance proves positivity of 23 and 30, and the
actual count-to-witness theorem supplies the family members. -/
theorem paperAxisProperArcSixCount_all_corners_of_positive
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (h0 : 0 < paperAxisProperArcSixCount g hg a ha 0)
    (h1 : 0 < paperAxisProperArcSixCount g hg a ha 1) :
    ∀ k : Fin 4, ∃ s : paperAxisProperEndpointTag g hg a,
      paperAxisProperEndpointSide g hg a ha s = k ∧
        paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a s) =
          paperQuadrilateralNextSide k := by
  have hb := paperAxisProperArcSixCount_corner_balance g hg a ha hproject
  have h2 : 0 < paperAxisProperArcSixCount g hg a ha 2 := by omega
  have h3 : 0 < paperAxisProperArcSixCount g hg a ha 3 := by omega
  have hpos (k : Fin 4) :
      0 < paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide k) := by
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  intro k
  obtain ⟨i, hi⟩ := (paperAxisProperArcPairCount_pos_iff g hg a ha k
    (paperQuadrilateralNextSide k)).mp (hpos k)
  rcases hi with hi | hi
  · refine ⟨(i, 0), hi.1, ?_⟩
    change paperAxisProperEndpointSide g hg a ha (i, 1) = _
    exact hi.2
  · refine ⟨(i, 1), hi.2, ?_⟩
    change paperAxisProperEndpointSide g hg a ha (i, 0) = _
    exact hi.1

/-- Actual positive corner counts imply actual ARC closure of the genuine
extrema set, discharging the old explicit ARC-closure premise geometrically. -/
theorem paperAxisExtremeEndpointSet_arc_closed_of_corner_positive
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (h0 : 0 < paperAxisProperArcSixCount g hg a ha 0)
    (h1 : 0 < paperAxisProperArcSixCount g hg a ha 1) :
    ∀ t ∈ paperAxisExtremeEndpointSet g hg a ha,
      paperAxisProperArcEndpointPair g hg a t ∈ paperAxisExtremeEndpointSet g hg a ha :=
  paperAxisExtremeEndpointSet_arc_closed_of_corner_arcs g hg a ha hproject
    (paperAxisProperArcSixCount_all_corners_of_positive g hg a ha hproject h0 h1)

/-- Positive actual adjacent corner counts force the actual entire connected
diagram to consist of actual side extrema. No classifier conclusion is made. -/
theorem paperAxisExtremeEndpointSet_eq_univ_of_corner_positive
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (h0 : 0 < paperAxisProperArcSixCount g hg a ha 0)
    (h1 : 0 < paperAxisProperArcSixCount g hg a ha 1) :
    paperAxisExtremeEndpointSet g hg a ha = Set.univ :=
  paperAxisExtremeEndpointSet_eq_univ_of_corner_arcs g hg a ha hproject
    (paperAxisProperArcSixCount_all_corners_of_positive g hg a ha hproject h0 h1)

end Markov
