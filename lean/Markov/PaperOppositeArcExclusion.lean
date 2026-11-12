import Markov.SquareOppositeArcCrossing
import Markov.PaperAxisProperSixArcCounts
import Markov.PaperQuadrilateralSquareEdges
import Markov.PaperQuadrilateralDiskChart

/-! Actual opposite-side proper Q-arcs must intersect through the literal raw
square chart and the concrete square crossing obstruction. Thus the genuine
proper family cannot contain both02 and13 arcs, and its actual corresponding
finite counts have product zero. No crossing/order/classification field is used. -/

noncomputable section
open Set Topology
namespace Markov

private theorem oppositeQ_interval_interior (t : unitInterval) (ht : ¬(t=0 ∨ t=1)) :
    0<(t:ℝ) ∧ (t:ℝ)<1 := by
  have h0 : (t:ℝ) ≠ 0 := fun h => ht (Or.inl (Subtype.ext h))
  have h1 : (t:ℝ) ≠ 1 := fun h => ht (Or.inr (Subtype.ext h))
  exact ⟨lt_of_le_of_ne t.property.1 h0.symm, lt_of_le_of_ne t.property.2 h1⟩

private theorem oppositeQ_orient_arc (q : C(unitInterval,paperIdealQuadrilateral)) (k l : Fin 4)
    (hend : ((q 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide k ∧
      (q 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide l) ∨
      ((q 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide l ∧
        (q 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide k))
    (hstrict : ∀ s : unitInterval, 0<(s:ℝ) → (s:ℝ)<1 →
      (q s:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion) :
    ∃ r : C(unitInterval,paperIdealQuadrilateral),
      (r 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide k ∧
      (r 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide l ∧
      range r=range q ∧
      ∀ s : unitInterval, 0<(s:ℝ) → (s:ℝ)<1 →
        (r s:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion := by
  rcases hend with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · exact ⟨q,h0,h1,rfl,hstrict⟩
  · let r : C(unitInterval,paperIdealQuadrilateral) :=
      ⟨fun s => q (unitInterval.symm s), q.continuous.comp unitInterval.continuous_symm⟩
    refine ⟨r,by simpa [r] using h1,by simpa [r] using h0,?_,?_⟩
    · ext z
      constructor
      · rintro ⟨s,rfl⟩
        exact ⟨unitInterval.symm s,rfl⟩
      · rintro ⟨s,rfl⟩
        refine ⟨unitInterval.symm s,?_⟩
        simp [r]
    · intro s hs0 hs1
      exact hstrict (unitInterval.symm s) (by change 0<1-(s:ℝ); linarith)
        (by change 1-(s:ℝ)<1; linarith)

private theorem oppositeQ_raw_injective : Function.Injective paperQuadrilateralComplexSquare := by
  intro z w h
  apply paperQuadrilateralSquareHomeomorph.injective
  apply Subtype.ext
  exact Prod.ext (congrArg Complex.re h) (congrArg Complex.im h)

private theorem oppositeQ_raw_strict (z : paperIdealQuadrilateral)
    (hz : (z:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion) :
    (-1<(paperQuadrilateralComplexSquare z).re ∧ (paperQuadrilateralComplexSquare z).re<1) ∧
      (-1<(paperQuadrilateralComplexSquare z).im ∧ (paperQuadrilateralComplexSquare z).im<1) := by
  have hside (k : Fin 4) : (z:UpperHalfPlane)∉paperQuadrilateralGeodesicSide k :=
    fun hk => (paperQuadrilateralGeodesicSide_subset_frontier k hk).2
      (paperIdealQuadrilateralStrictRegion_subset_interior hz)
  have hA1 : paperSquareChartA z ≠ 1 := fun h => hside 1 ((paperSquareChartA_eq_one_iff z).mp h)
  have hAm : paperSquareChartA z ≠ -1 := fun h => hside 3 ((paperSquareChartA_eq_neg_one_iff z).mp h)
  have hB1 : paperSquareChartB z ≠ 1 := fun h => hside 0 ((paperSquareChartB_eq_one_iff z).mp h)
  have hBm : paperSquareChartB z ≠ -1 := fun h => hside 2 ((paperSquareChartB_eq_neg_one_iff z).mp h)
  have h := paperSquareChart_mem z
  obtain ⟨hAl,hAr⟩ := abs_le.mp h.1
  obtain ⟨hBl,hBr⟩ := abs_le.mp h.2.1
  exact ⟨⟨lt_of_le_of_ne hAl hAm.symm,lt_of_le_of_ne hAr hA1⟩,
    ⟨lt_of_le_of_ne hBl hBm.symm,lt_of_le_of_ne hBr hB1⟩⟩

/-- Actual continuous proper Q-arcs joining02 and13 intersect, in either
orientation. The crossing witness is constructed through the actual raw square
chart, not supplied as a boundary-order or chord-intersection premise. -/
theorem paperQuadrilateral_opposite_side_arcs_intersect
    (q r : C(unitInterval,paperIdealQuadrilateral))
    (h02 : ((q 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 0 ∧
      (q 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 2) ∨
      ((q 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 2 ∧
        (q 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 0))
    (h13 : ((r 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 1 ∧
      (r 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 3) ∨
      ((r 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 3 ∧
        (r 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 1))
    (hq : ∀ s : unitInterval, 0<(s:ℝ) → (s:ℝ)<1 →
      (q s:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion)
    (hr : ∀ s : unitInterval, 0<(s:ℝ) → (s:ℝ)<1 →
      (r s:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion) :
    ∃ s t : unitInterval, q s=r t := by
  obtain ⟨f,hf0,hf1,hfq,hfstrict⟩ := oppositeQ_orient_arc q 0 2 h02 hq
  obtain ⟨g,hg0,hg1,hgr,hgstrict⟩ := oppositeQ_orient_arc r 1 3 h13 hr
  have hf0' : (paperQuadrilateralComplexSquare (f 0)).im=1 := (paperSquareChartB_eq_one_iff _).mpr hf0
  have hf1' : (paperQuadrilateralComplexSquare (f 1)).im= -1 := (paperSquareChartB_eq_neg_one_iff _).mpr hf1
  have hg0' : (paperQuadrilateralComplexSquare (g 0)).re=1 := (paperSquareChartA_eq_one_iff _).mpr hg0
  have hg1' : (paperQuadrilateralComplexSquare (g 1)).re= -1 := (paperSquareChartA_eq_neg_one_iff _).mpr hg1
  have hfx (s : unitInterval) : -1<(paperQuadrilateralComplexSquare (f s)).re ∧
      (paperQuadrilateralComplexSquare (f s)).re<1 := by
    by_cases hs : s=0 ∨ s=1
    · rcases hs with rfl | rfl
      · exact paperPuncturedSquare_horizontal_param (paperQuadrilateralToSquare (f 0)) (Or.inl hf0')
      · exact paperPuncturedSquare_horizontal_param (paperQuadrilateralToSquare (f 1)) (Or.inr hf1')
    · obtain ⟨hs0,hs1⟩ := oppositeQ_interval_interior s hs
      exact (oppositeQ_raw_strict _ (hfstrict s hs0 hs1)).1
  have hgy (s : unitInterval) : -1<(paperQuadrilateralComplexSquare (g s)).im ∧
      (paperQuadrilateralComplexSquare (g s)).im<1 := by
    by_cases hs : s=0 ∨ s=1
    · rcases hs with rfl | rfl
      · exact paperPuncturedSquare_vertical_param (paperQuadrilateralToSquare (g 0)) (Or.inl hg0')
      · exact paperPuncturedSquare_vertical_param (paperQuadrilateralToSquare (g 1)) (Or.inr hg1')
    · obtain ⟨hs0,hs1⟩ := oppositeQ_interval_interior s hs
      exact (oppositeQ_raw_strict _ (hgstrict s hs0 hs1)).2
  obtain ⟨s,t,hst⟩ := squareArcs_top_bottom_right_left_intersect
    (paperQuadrilateralComplexSquare ∘ f) (paperQuadrilateralComplexSquare ∘ g)
    (continuous_paperQuadrilateralComplexSquare.comp f.continuous)
    (continuous_paperQuadrilateralComplexSquare.comp g.continuous)
    hf0' hf1' hg0' hg1' hfx hgy
  have heq : f s=g t := oppositeQ_raw_injective hst
  have hzq : f s∈range q := hfq ▸ ⟨s,rfl⟩
  have hzr : f s∈range r := hgr ▸ ⟨t,heq.symm⟩
  obtain ⟨u,hu⟩ := hzq
  obtain ⟨v,hv⟩ := hzr
  exact ⟨u,v,hu.trans hv.symm⟩

/-- The genuine actually disjoint proper family cannot contain both an02 and
an13 arc. Endpoint-side memberships and the intersection are all actual. -/
theorem paperAxisProperArc_opposite_pairs_not_coexist
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a∉paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun t : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg t))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (i j : paperAxisProperArcIndex g hg a)
    (h02 : (paperAxisProperEndpointSide g hg a ha (i,0)=0 ∧
      paperAxisProperEndpointSide g hg a ha (i,1)=2) ∨
      (paperAxisProperEndpointSide g hg a ha (i,0)=2 ∧
        paperAxisProperEndpointSide g hg a ha (i,1)=0))
    (h13 : (paperAxisProperEndpointSide g hg a ha (j,0)=1 ∧
      paperAxisProperEndpointSide g hg a ha (j,1)=3) ∨
      (paperAxisProperEndpointSide g hg a ha (j,0)=3 ∧
        paperAxisProperEndpointSide g hg a ha (j,1)=1)) : False := by
  have hij : i≠j := by
    intro heq
    subst j
    rcases h02 with ⟨hi,_⟩ | ⟨hi,_⟩ <;> rcases h13 with ⟨hj,_⟩ | ⟨hj,_⟩ <;>
      have h := hi.symm.trans hj <;> have hv := congrArg Fin.val h <;> norm_num at hv
  have sides (k : paperAxisProperArcIndex g hg a) (u v : Fin 4)
      (h : (paperAxisProperEndpointSide g hg a ha (k,0)=u ∧
        paperAxisProperEndpointSide g hg a ha (k,1)=v) ∨
        (paperAxisProperEndpointSide g hg a ha (k,0)=v ∧
          paperAxisProperEndpointSide g hg a ha (k,1)=u)) :
      ((paperAxisProperArc g hg a ha k 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide u ∧
        (paperAxisProperArc g hg a ha k 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide v) ∨
      ((paperAxisProperArc g hg a ha k 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide v ∧
        (paperAxisProperArc g hg a ha k 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide u) := by
    have h0 := paperAxisProperEndpointSide_spec g hg a ha (k,0)
    have h1 := paperAxisProperEndpointSide_spec g hg a ha (k,1)
    rcases h with ⟨h0',h1'⟩ | ⟨h0',h1'⟩
    · exact Or.inl ⟨h0' ▸ h0,h1' ▸ h1⟩
    · exact Or.inr ⟨h0' ▸ h0,h1' ▸ h1⟩
  obtain ⟨s,t,hst⟩ := paperQuadrilateral_opposite_side_arcs_intersect
    (paperAxisProperArc g hg a ha i) (paperAxisProperArc g hg a ha j)
    (sides i 0 2 h02) (sides j 1 3 h13)
    (paperAxisProperArc_strict g hg a ha i) (paperAxisProperArc_strict g hg a ha j)
  exact paperAxisProperArc_points_ne g hg a ha hproject i j hij s t hst

/-- Genuine actual opposite-family arc counts have product zero. This is
derived from actual arc witnesses, not assumed as a normal-count constraint. -/
theorem paperAxisProperArc_opposite_pairCount_mul_eq_zero
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a∉paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun t : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg t))
      (Ioo b (b+modularClosedGeodesicPeriod g))) :
    paperAxisProperArcPairCount g hg a ha 0 2 * paperAxisProperArcPairCount g hg a ha 1 3=0 := by
  by_cases h02 : paperAxisProperArcPairCount g hg a ha 0 2=0
  · simp only [h02,zero_mul]
  have h13 : paperAxisProperArcPairCount g hg a ha 1 3=0 := by
    by_contra h13
    obtain ⟨i,hi⟩ := (paperAxisProperArcPairCount_pos_iff g hg a ha 0 2).mp (Nat.pos_of_ne_zero h02)
    obtain ⟨j,hj⟩ := (paperAxisProperArcPairCount_pos_iff g hg a ha 1 3).mp (Nat.pos_of_ne_zero h13)
    exact paperAxisProperArc_opposite_pairs_not_coexist g hg a ha hproject i j hi hj
  simp only [h13,mul_zero]

/-- In the actual six-count order[01,12,23,30,02,13], the last two entries
satisfy the genuine geometric zero-product constraint. -/
theorem paperAxisProperArcSixCount_opposite_mul_eq_zero
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a∉paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun t : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg t))
      (Ioo b (b+modularClosedGeodesicPeriod g))) :
    paperAxisProperArcSixCount g hg a ha 4 * paperAxisProperArcSixCount g hg a ha 5=0 := by
  change paperAxisProperArcPairCount g hg a ha 0 2 * paperAxisProperArcPairCount g hg a ha 1 3=0
  exact paperAxisProperArc_opposite_pairCount_mul_eq_zero g hg a ha hproject

end Markov
