import Markov.RawSquareCornerCap
import Markov.PaperAxisSortedExtremalRanks
import Markov.PaperAxisTaggedOrientedArcs
import Markov.PaperQuadrilateralBoundaryOrientation

/-! Actual nearest TOP/RIGHT endpoint pairing follows from actual cap crossing.
Extremal inequalities in the final theorem come from the actual sorted side
lists; no nearest-pair or order-preserving ARC field is assumed. -/
noncomputable section
open Set Topology
namespace Markov

private theorem nearest_side_mem
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a) (k : Fin 4)
    (ht : paperAxisProperEndpointSide g hg a ha t = k) :
    t ∈ paperAxisProperEndpointSideTags g hg a ha k := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩

private theorem nearest_tag_eq_of_coordinate_eq
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (s t : paperAxisProperEndpointTag g hg a) (k : Fin 4)
    (hs : paperAxisProperEndpointSide g hg a ha s = k)
    (ht : paperAxisProperEndpointSide g hg a ha t = k)
    (hc : paperAxisProperEndpointCoordinate g hg a ha s = paperAxisProperEndpointCoordinate g hg a ha t) : s=t :=
  paperAxisProperEndpointCoordinate_injOn_side g hg a ha hproject k
    (nearest_side_mem g hg a ha s k hs) (nearest_side_mem g hg a ha t k ht) hc

private theorem nearest_top_raw
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a)
    (ht : paperAxisProperEndpointSide g hg a ha t = 0) :
    (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha t)).re =
        paperAxisProperEndpointCoordinate g hg a ha t ∧
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha t)).im = 1 := by
  have hm : (paperAxisProperEndpointPoint g hg a ha t : UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide 0 := by
    simpa only [ht] using paperAxisProperEndpointSide_spec g hg a ha t
  constructor
  · have he := paperQuadrilateralMarkedSideCoordinate_raw_formula 0 _ hm
    change paperQuadrilateralRawSideCoordinate 0 (paperAxisProperEndpointPoint g hg a ha t) = _
    unfold paperAxisProperEndpointCoordinate
    rw [ht]
    symm
    simpa only [if_pos (Or.inl rfl)] using he
  · exact (paperSquareChartB_eq_one_iff _).mpr hm

private theorem nearest_right_raw
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a)
    (ht : paperAxisProperEndpointSide g hg a ha t = 1) :
    (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha t)).im =
        paperAxisProperEndpointCoordinate g hg a ha t ∧
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha t)).re = 1 := by
  have hm : (paperAxisProperEndpointPoint g hg a ha t : UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide 1 := by
    simpa only [ht] using paperAxisProperEndpointSide_spec g hg a ha t
  constructor
  · have he := paperQuadrilateralMarkedSideCoordinate_raw_formula 1 _ hm
    change paperQuadrilateralRawSideCoordinate 1 (paperAxisProperEndpointPoint g hg a ha t) = _
    unfold paperAxisProperEndpointCoordinate
    rw [ht]
    symm
    simpa only [if_pos (Or.inr rfl)] using he
  · exact (paperSquareChartA_eq_one_iff _).mpr hm

private theorem nearest_cap_nonnegative_sides (x y : ℝ) (hx : -1<x ∧ x<1) (hy : -1<y ∧ y<1)
    (z : paperIdealQuadrilateral) (k : Fin 4) (hz : (z:UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide k)
    (hc : 0 ≤ rawSquareCorner01Cap x y (paperQuadrilateralComplexSquare z)) : k=0 ∨ k=1 := by
  have hb := paperSquareChart_mem z
  fin_cases k
  · exact Or.inl rfl
  · exact Or.inr rfl
  · have hbottom : (paperQuadrilateralComplexSquare z).im = -1 := (paperSquareChartB_eq_neg_one_iff _).mpr hz
    have hre : (paperQuadrilateralComplexSquare z).re ≤ 1 := (abs_le.mp hb.1).2
    have hp := mul_pos (sub_pos.mpr hx.2) (show 0<1+y by linarith [hy.1])
    have hd := mul_nonneg (sub_pos.mpr hy.2).le (sub_nonneg.mpr hre)
    dsimp only [rawSquareCorner01Cap] at hc
    rw [hbottom] at hc
    exfalso
    nlinarith
  · have hleft : (paperQuadrilateralComplexSquare z).re = -1 := (paperSquareChartA_eq_neg_one_iff _).mpr hz
    have him : (paperQuadrilateralComplexSquare z).im ≤ 1 := (abs_le.mp hb.2.1).2
    have hp := mul_pos (sub_pos.mpr hy.2) (show 0<1+x by linarith [hx.1])
    have hd := mul_nonneg (sub_pos.mpr hx.2).le (sub_nonneg.mpr him)
    dsimp only [rawSquareCorner01Cap] at hc
    rw [hleft] at hc
    exfalso
    nlinarith

/-- Genuine cap crossing and full actual arc separation force the other
endpoint of any different actual arc entering the positive cap to stay
nonnegative. The conclusion is derived, never an assumed packet property. -/
theorem paperAxisCorner01_cap_partner_nonnegative
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (s t : paperAxisProperEndpointTag g hg a)
    (hs0 : paperAxisProperEndpointSide g hg a ha s = 0)
    (hs1 : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a s) = 1)
    (hindices : s.1 ≠ t.1)
    (hpos : 0 < rawSquareCorner01Cap
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha s)).re
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha t))) :
    0 ≤ rawSquareCorner01Cap
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha s)).re
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t))) := by
  by_contra hn
  have hneg := lt_of_not_ge hn
  let q := (paperAxisArcFromTag g hg a ha s).toContinuousMap
  let r := (paperAxisArcFromTag g hg a ha t).toContinuousMap
  have hq0 : q 0 = paperAxisProperEndpointPoint g hg a ha s := (paperAxisArcFromTag g hg a ha s).source
  have hq1 : q 1 = paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s) := (paperAxisArcFromTag g hg a ha s).target
  have hr0 : r 0 = paperAxisProperEndpointPoint g hg a ha t := (paperAxisArcFromTag g hg a ha t).source
  have hr1 : r 1 = paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t) := (paperAxisArcFromTag g hg a ha t).target
  obtain ⟨u,v,he⟩ := paperQuadrilateral_corner01_cap_arcs_intersect q r
    (by rw [hq0]; simpa only [hs0] using paperAxisProperEndpointSide_spec g hg a ha s)
    (by rw [hq1]; simpa only [hs1] using paperAxisProperEndpointSide_spec g hg a ha (paperAxisProperArcEndpointPair g hg a s))
    (paperAxisProperEndpointSide g hg a ha t)
    (paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t))
    (paperAxisProperArcEndpointPair_sides_ne g hg a ha t).symm
    (by rw [hr0]; exact paperAxisProperEndpointSide_spec g hg a ha t)
    (by rw [hr1]; exact paperAxisProperEndpointSide_spec g hg a ha (paperAxisProperArcEndpointPair g hg a t))
    (fun z hz0 hz1 => paperAxisArcFromTag_strict g hg a ha s z hz0 hz1)
    (fun z hz0 hz1 => paperAxisArcFromTag_strict g hg a ha t z hz0 hz1)
    (by rw [hq0,hq1,hr0]; exact hpos)
    (by rw [hq0,hq1,hr1]; exact hneg)
  exact paperAxisArcFromTag_points_ne g hg a ha hproject s t hindices u v he

/-- A TOP endpoint nearer the top-right corner than an actual TOP-to-RIGHT
arc must partner to a RIGHT endpoint still nearer that corner. -/
theorem paperAxisCorner01_top_nearer_partner
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (s t : paperAxisProperEndpointTag g hg a)
    (hs0 : paperAxisProperEndpointSide g hg a ha s = 0)
    (hs1 : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a s) = 1)
    (ht0 : paperAxisProperEndpointSide g hg a ha t = 0)
    (hlt : paperAxisProperEndpointCoordinate g hg a ha s < paperAxisProperEndpointCoordinate g hg a ha t) :
    paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) = 1 ∧
      paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a s) <
        paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a t) := by
  have hne : s ≠ t := by intro he; subst t; exact (lt_irrefl _) hlt
  have hi := paperAxisProperEndpoint_same_side_arcIndex_ne g hg a ha s t hne (hs0.trans ht0.symm)
  have hs := nearest_top_raw g hg a ha s hs0
  have hp := nearest_right_raw g hg a ha (paperAxisProperArcEndpointPair g hg a s) hs1
  have ht := nearest_top_raw g hg a ha t ht0
  have hpos : 0 < rawSquareCorner01Cap
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha s)).re
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha t)) := by
    simpa only [rawSquareCorner01Cap,hs.1,hp.1,ht.1,ht.2,sub_self,mul_zero,add_zero] using
      mul_pos (sub_pos.mpr (paperAxisProperEndpointCoordinate_bounds g hg a ha (paperAxisProperArcEndpointPair g hg a s)).2)
        (sub_pos.mpr hlt)
  have hc := paperAxisCorner01_cap_partner_nonnegative g hg a ha hproject s t hs0 hs1 hi hpos
  have ha0 := paperAxisProperEndpointCoordinate_bounds g hg a ha s
  have ha1 := paperAxisProperEndpointCoordinate_bounds g hg a ha (paperAxisProperArcEndpointPair g hg a s)
  have hcases := nearest_cap_nonnegative_sides _ _
    (by simpa only [hs.1] using ha0) (by simpa only [hp.1] using ha1)
    (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t)) _
    (paperAxisProperEndpointSide_spec g hg a ha (paperAxisProperArcEndpointPair g hg a t)) hc
  have ht1 : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) = 1 := by
    rcases hcases with h0 | h1
    · exact False.elim ((paperAxisProperArcEndpointPair_sides_ne g hg a ha t) (h0.trans ht0.symm))
    · exact h1
  have hpt := nearest_right_raw g hg a ha (paperAxisProperArcEndpointPair g hg a t) ht1
  have heq : rawSquareCorner01Cap
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha s)).re
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t))) =
      (1-paperAxisProperEndpointCoordinate g hg a ha s)*
        (paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a t)-
          paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a s)) := by
    rw [rawSquareCorner01Cap,hs.1,hp.1,hpt.1,hpt.2]
    ring
  rw [heq] at hc
  have hle : paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a s) ≤
      paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a t) := by
    by_contra hn
    exact not_lt_of_ge hc (mul_neg_of_pos_of_neg (sub_pos.mpr ha0.2) (sub_neg.mpr (lt_of_not_ge hn)))
  refine ⟨ht1,lt_of_le_of_ne hle ?_⟩
  intro he
  exact hne ((paperAxisProperArcEndpointPair g hg a).injective
    (nearest_tag_eq_of_coordinate_eq g hg a ha hproject _ _ 1 hs1 ht1 he))

/-- The analogous actual packet statement for a RIGHT endpoint nearer the
same corner, derived from the SAME actual positive-to-negative cap obstruction. -/
theorem paperAxisCorner01_right_nearer_partner
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (s t : paperAxisProperEndpointTag g hg a)
    (hs0 : paperAxisProperEndpointSide g hg a ha s = 0)
    (hs1 : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a s) = 1)
    (ht1 : paperAxisProperEndpointSide g hg a ha t = 1)
    (hlt : paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a s) <
      paperAxisProperEndpointCoordinate g hg a ha t) :
    paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) = 0 ∧
      paperAxisProperEndpointCoordinate g hg a ha s <
        paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a t) := by
  have hne : paperAxisProperArcEndpointPair g hg a s ≠ t := by
    intro he; rw [he] at hlt; exact (lt_irrefl _) hlt
  have hi : s.1 ≠ t.1 := paperAxisProperEndpoint_same_side_arcIndex_ne g hg a ha
    (paperAxisProperArcEndpointPair g hg a s) t hne (hs1.trans ht1.symm)
  have hs := nearest_top_raw g hg a ha s hs0
  have hp := nearest_right_raw g hg a ha (paperAxisProperArcEndpointPair g hg a s) hs1
  have ht := nearest_right_raw g hg a ha t ht1
  have heq0 : rawSquareCorner01Cap
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha s)).re
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha t)) =
      (1-paperAxisProperEndpointCoordinate g hg a ha s)*
        (paperAxisProperEndpointCoordinate g hg a ha t-
          paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a s)) := by
    rw [rawSquareCorner01Cap,hs.1,hp.1,ht.1,ht.2]
    ring
  have hpos : 0 < rawSquareCorner01Cap
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha s)).re
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha t)) := by
    rw [heq0]
    exact mul_pos (sub_pos.mpr (paperAxisProperEndpointCoordinate_bounds g hg a ha s).2) (sub_pos.mpr hlt)
  have hc := paperAxisCorner01_cap_partner_nonnegative g hg a ha hproject s t hs0 hs1 hi hpos
  have ha0 := paperAxisProperEndpointCoordinate_bounds g hg a ha s
  have ha1 := paperAxisProperEndpointCoordinate_bounds g hg a ha (paperAxisProperArcEndpointPair g hg a s)
  have hcases := nearest_cap_nonnegative_sides _ _
    (by simpa only [hs.1] using ha0) (by simpa only [hp.1] using ha1)
    (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t)) _
    (paperAxisProperEndpointSide_spec g hg a ha (paperAxisProperArcEndpointPair g hg a t)) hc
  have ht0 : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) = 0 := by
    rcases hcases with h0 | h1
    · exact h0
    · exact False.elim ((paperAxisProperArcEndpointPair_sides_ne g hg a ha t) (h1.trans ht1.symm))
  have hpt := nearest_top_raw g hg a ha (paperAxisProperArcEndpointPair g hg a t) ht0
  have heq : rawSquareCorner01Cap
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha s)).re
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im
      (paperQuadrilateralComplexSquare (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t))) =
      (1-paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a s))*
        (paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a t)-
          paperAxisProperEndpointCoordinate g hg a ha s) := by
    simp only [rawSquareCorner01Cap,hs.1,hp.1,hpt.1,hpt.2,sub_self,mul_zero,add_zero]
  rw [heq] at hc
  have hle : paperAxisProperEndpointCoordinate g hg a ha s ≤
      paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a t) := by
    by_contra hn
    exact not_lt_of_ge hc (mul_neg_of_pos_of_neg (sub_pos.mpr ha1.2) (sub_neg.mpr (lt_of_not_ge hn)))
  refine ⟨ht0,lt_of_le_of_ne hle ?_⟩
  intro he
  have htag := nearest_tag_eq_of_coordinate_eq g hg a ha hproject s
    (paperAxisProperArcEndpointPair g hg a t) 0 hs0 ht0 he
  have htEq : t = paperAxisProperArcEndpointPair g hg a s := by
    calc
      t = paperAxisProperArcEndpointPair g hg a (paperAxisProperArcEndpointPair g hg a t) :=
        (paperAxisProperArcEndpointPair_involutive g hg a t).symm
      _ = paperAxisProperArcEndpointPair g hg a s := congrArg (paperAxisProperArcEndpointPair g hg a) htag.symm
  exact hne htEq.symm

/-- If the actual diagram has any TOP/RIGHT corner arc, its actual maximal
TOP and maximal RIGHT endpoints MUST be ARC-paired. No nearest-pair field is assumed. -/
theorem paperAxisCorner01_maxima_arc_paired
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (t u : paperAxisProperEndpointTag g hg a)
    (ht : paperAxisProperEndpointSide g hg a ha t = 0)
    (hu : paperAxisProperEndpointSide g hg a ha u = 1)
    (hmaxT : ∀ v, paperAxisProperEndpointSide g hg a ha v = 0 →
      paperAxisProperEndpointCoordinate g hg a ha v ≤ paperAxisProperEndpointCoordinate g hg a ha t)
    (hmaxR : ∀ v, paperAxisProperEndpointSide g hg a ha v = 1 →
      paperAxisProperEndpointCoordinate g hg a ha v ≤ paperAxisProperEndpointCoordinate g hg a ha u)
    (hcorner : ∃ s : paperAxisProperEndpointTag g hg a,
      paperAxisProperEndpointSide g hg a ha s = 0 ∧
        paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a s) = 1) :
    paperAxisProperArcEndpointPair g hg a t = u := by
  obtain ⟨s,hs0,hs1⟩ := hcorner
  have ht1 : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) = 1 := by
    by_cases he : s=t
    · simpa only [he] using hs1
    · have hneq : paperAxisProperEndpointCoordinate g hg a ha s ≠ paperAxisProperEndpointCoordinate g hg a ha t :=
        fun hc => he (nearest_tag_eq_of_coordinate_eq g hg a ha hproject s t 0 hs0 ht hc)
      exact (paperAxisCorner01_top_nearer_partner g hg a ha hproject s t hs0 hs1 ht
        (lt_of_le_of_ne (hmaxT s hs0) hneq)).1
  by_contra he
  have hneq : paperAxisProperEndpointCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a t) ≠
      paperAxisProperEndpointCoordinate g hg a ha u :=
    fun hc => he (nearest_tag_eq_of_coordinate_eq g hg a ha hproject _ u 1 ht1 hu hc)
  have hnear := paperAxisCorner01_right_nearer_partner g hg a ha hproject t u ht ht1 hu
    (lt_of_le_of_ne (hmaxR _ ht1) hneq)
  exact not_lt_of_ge (hmaxT _ hnear.1) hnear.2

/-- The actual finite side sorts construct the two corner-nearest ranks and
prove their ARC pairing from genuine corner-arc existence and actual crossing. -/
theorem paperAxisCorner01_sorted_last_arc_paired
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (hcorner : ∃ s : paperAxisProperEndpointTag g hg a,
      paperAxisProperEndpointSide g hg a ha s = 0 ∧
        paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a s) = 1) :
    ∃ (h0 : 0 < (paperAxisProperEndpointSideCoordinates g hg a ha 0).card)
      (h1 : 0 < (paperAxisProperEndpointSideCoordinates g hg a ha 1).card),
      paperAxisProperArcEndpointPair g hg a
        (paperAxisProperEndpointSortedTag g hg a ha 0
          ⟨(paperAxisProperEndpointSideCoordinates g hg a ha 0).card-1,Nat.sub_lt h0 (by decide)⟩) =
        paperAxisProperEndpointSortedTag g hg a ha 1
          ⟨(paperAxisProperEndpointSideCoordinates g hg a ha 1).card-1,Nat.sub_lt h1 (by decide)⟩ := by
  classical
  have hpos (k : Fin 4) (t : paperAxisProperEndpointTag g hg a)
      (ht : paperAxisProperEndpointSide g hg a ha t = k) :
      0 < (paperAxisProperEndpointSideCoordinates g hg a ha k).card := by
    have hr : t ∈ Set.range (paperAxisProperEndpointSortedTag g hg a ha k) := by
      rw [paperAxisProperEndpointSortedTag_range g hg a ha hproject]
      exact nearest_side_mem g hg a ha t k ht
    obtain ⟨i,_⟩ := hr
    exact Nat.zero_lt_of_lt i.isLt
  obtain ⟨s,hs0,hs1⟩ := hcorner
  let h0 := hpos 0 s hs0
  let h1 := hpos 1 (paperAxisProperArcEndpointPair g hg a s) hs1
  refine ⟨h0,h1,?_⟩
  apply paperAxisCorner01_maxima_arc_paired g hg a ha hproject
  · exact (Finset.mem_filter.mp (paperAxisProperEndpointSortedTag_spec g hg a ha 0 _).1).2
  · exact (Finset.mem_filter.mp (paperAxisProperEndpointSortedTag_spec g hg a ha 1 _).1).2
  · exact fun v hv => paperAxisProperEndpointSortedTag_le_last g hg a ha hproject 0 h0 v hv
  · exact fun v hv => paperAxisProperEndpointSortedTag_le_last g hg a ha hproject 1 h1 v hv
  · exact ⟨s,hs0,hs1⟩

end Markov
