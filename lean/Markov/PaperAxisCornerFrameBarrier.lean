import Markov.RawSquareCornerCap
import Markov.PaperQuadrilateralRawSideFrame
import Markov.PaperAxisTaggedOrientedArcs

/-! Actual positive-cap barriers in every literal Q corner. Complex quarter
turns transport constructed chord data; topology is applied to the ORIGINAL
actual Q arcs. No surface isometry, corner order or pairing field is assumed. -/
noncomputable section
open Set Topology
namespace Markov

/-- A boundary Q-point nonnegative in an actual selected corner cap must lie
on that selected side or its literal next side. This is actual raw-coordinate
geometry, not a normal-diagram field. -/
theorem paperQuadrilateralFrame_nonnegative_cap_sides
    (k : Fin 4) (x y : ℝ) (hx : -1<x ∧ x<1) (hy : -1<y ∧ y<1)
    (z : paperIdealQuadrilateral) (j : Fin 4)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide j)
    (hc : 0 ≤ rawSquareCorner01Cap x y (paperQuadrilateralRawSideFrame k z)) :
    j=k ∨ j=paperQuadrilateralNextSide k := by
  have hraw : (-1≤(paperQuadrilateralComplexSquare z).re ∧ (paperQuadrilateralComplexSquare z).re≤1) ∧
      (-1≤(paperQuadrilateralComplexSquare z).im ∧ (paperQuadrilateralComplexSquare z).im≤1) := by
    have hb := paperSquareChart_mem z
    exact ⟨abs_le.mp hb.1,abs_le.mp hb.2.1⟩
  have hb := rawSquareQuarterTurn_closed_coordinates k (paperQuadrilateralComplexSquare z) hraw
  change (-1≤(paperQuadrilateralRawSideFrame k z).re ∧ (paperQuadrilateralRawSideFrame k z).re≤1) ∧
    (-1≤(paperQuadrilateralRawSideFrame k z).im ∧ (paperQuadrilateralRawSideFrame k z).im≤1) at hb
  have hm := (paperQuadrilateralRawSideFrame_side_iff k j z).mpr hz
  by_contra hn
  have hn0 : j ≠ k := fun h => hn (Or.inl h)
  have hn1 : j ≠ paperQuadrilateralNextSide k := fun h => hn (Or.inr h)
  have hr : (j-k : Fin 4)=2 ∨ (j-k : Fin 4)=3 := by
    fin_cases k <;> fin_cases j
    all_goals first | exact Or.inl rfl | exact Or.inr rfl | exact False.elim (hn0 rfl) | exact False.elim (hn1 rfl)
  rcases hr with hr | hr
  · rw [hr] at hm
    have hbottom : (paperQuadrilateralRawSideFrame k z).im = -1 := hm
    have hp := mul_pos (sub_pos.mpr hx.2) (show 0<1+y by linarith [hy.1])
    have hd := mul_nonneg (sub_pos.mpr hy.2).le (sub_nonneg.mpr hb.1.2)
    dsimp only [rawSquareCorner01Cap] at hc
    rw [hbottom] at hc
    nlinarith
  · rw [hr] at hm
    have hleft : (paperQuadrilateralRawSideFrame k z).re = -1 := hm
    have hp := mul_pos (sub_pos.mpr hy.2) (show 0<1+x by linarith [hx.1])
    have hd := mul_nonneg (sub_pos.mpr hx.2).le (sub_nonneg.mpr hb.2.2)
    dsimp only [rawSquareCorner01Cap] at hc
    rw [hleft] at hc
    nlinarith

/-- In EVERY actual Q corner, genuine cap crossing and full actual arc
separation force the partner of a different arc entering the positive cap to
remain nonnegative. Constructed rotated chord data is transported back before
the actual RAW-square crossing theorem is used. -/
theorem paperAxisCorner_cap_partner_nonnegative
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (k : Fin 4) (s t : paperAxisProperEndpointTag g hg a)
    (hs0 : paperAxisProperEndpointSide g hg a ha s = k)
    (hs1 : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a s) = paperQuadrilateralNextSide k)
    (hindices : s.1 ≠ t.1)
    (hpos : 0 < rawSquareCorner01Cap
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha s)).re
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha t))) :
    0 ≤ rawSquareCorner01Cap
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha s)).re
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t))) := by
  by_contra hn
  have hneg := lt_of_not_ge hn
  let q := (paperAxisArcFromTag g hg a ha s).toContinuousMap
  let r := (paperAxisArcFromTag g hg a ha t).toContinuousMap
  let f : unitInterval → ℂ := rawSquareQuarterTurn k ∘ (paperQuadrilateralComplexSquare ∘ q)
  let h : unitInterval → ℂ := rawSquareQuarterTurn k ∘ (paperQuadrilateralComplexSquare ∘ r)
  have hq0 : q 0 = paperAxisProperEndpointPoint g hg a ha s := (paperAxisArcFromTag g hg a ha s).source
  have hq1 : q 1 = paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s) := (paperAxisArcFromTag g hg a ha s).target
  have hr0 : r 0 = paperAxisProperEndpointPoint g hg a ha t := (paperAxisArcFromTag g hg a ha t).source
  have hr1 : r 1 = paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t) := (paperAxisArcFromTag g hg a ha t).target
  have hq0side : (q 0:UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide k := by
    rw [hq0]; simpa only [hs0] using paperAxisProperEndpointSide_spec g hg a ha s
  have hq1side : (q 1:UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide (paperQuadrilateralNextSide k) := by
    rw [hq1]; simpa only [hs1] using paperAxisProperEndpointSide_spec g hg a ha (paperAxisProperArcEndpointPair g hg a s)
  have hr0side : (r 0:UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide (paperAxisProperEndpointSide g hg a ha t) := by
    rw [hr0]; exact paperAxisProperEndpointSide_spec g hg a ha t
  have hr1side : (r 1:UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide
      (paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t)) := by
    rw [hr1]; exact paperAxisProperEndpointSide_spec g hg a ha (paperAxisProperArcEndpointPair g hg a t)
  have hmn : paperAxisProperEndpointSide g hg a ha t ≠
      paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) :=
    (paperAxisProperArcEndpointPair_sides_ne g hg a ha t).symm
  have hf0 : (f 0).im=1 := (paperQuadrilateralRawSideFrame_top k (q 0) hq0side).1
  have hf1 : (f 1).re=1 := (paperQuadrilateralRawSideFrame_right k (q 1) hq1side).1
  have hfa : -1<(f 0).re ∧ (f 0).re<1 := by
    change -1<(paperQuadrilateralRawSideFrame k (q 0)).re ∧ (paperQuadrilateralRawSideFrame k (q 0)).re<1
    rw [paperQuadrilateralRawSideFrame_re]
    exact paperQuadrilateralRawBoundarySideCoordinate_bounds k (q 0) hq0side
  have hfb : -1<(f 1).im ∧ (f 1).im<1 := by
    change -1<(paperQuadrilateralRawSideFrame k (q 1)).im ∧ (paperQuadrilateralRawSideFrame k (q 1)).im<1
    rw [paperQuadrilateralRawSideFrame_im]
    have hb := paperQuadrilateralRawBoundarySideCoordinate_bounds _ (q 1) hq1side
    constructor <;> linarith [hb.1,hb.2]
  have hp : 0<rawSquareCorner01Cap (f 0).re (f 1).im (h 0) := by
    change 0<rawSquareCorner01Cap (paperQuadrilateralRawSideFrame k (q 0)).re
      (paperQuadrilateralRawSideFrame k (q 1)).im (paperQuadrilateralRawSideFrame k (r 0))
    rw [hq0,hq1,hr0]
    exact hpos
  have hn' : rawSquareCorner01Cap (f 0).re (f 1).im (h 1)<0 := by
    change rawSquareCorner01Cap (paperQuadrilateralRawSideFrame k (q 0)).re
      (paperQuadrilateralRawSideFrame k (q 1)).im (paperQuadrilateralRawSideFrame k (r 1))<0
    rw [hq0,hq1,hr1]
    exact hneg
  have hch : ∀ v : unitInterval, 0<(v:ℝ) → (v:ℝ)<1 →
      (-1<(diskArcChord h v).re ∧ (diskArcChord h v).re<1) ∧
      (-1<(diskArcChord h v).im ∧ (diskArcChord h v).im<1) := by
    intro v hv0 hv1
    have hb := paperQuadrilateral_raw_chord_strict_coordinates r _ _ hmn hr0side hr1side v hv0 hv1
    have ht := rawSquareQuarterTurn_strict_coordinates k
      (diskArcChord (paperQuadrilateralComplexSquare ∘ r) v) hb
    simpa only [h,rawSquareQuarterTurn_diskArcChord] using ht
  obtain ⟨u,v,hu0,hu1,hv0,hv1,hd,hc⟩ := rawSquareCorner01Chord_data f h hf0 hf1 hfa hfb hp hn' hch
  have hd' : (paperQuadrilateralComplexSquare (q 1)-paperQuadrilateralComplexSquare (q 0)).re *
      (paperQuadrilateralComplexSquare (r 1)-paperQuadrilateralComplexSquare (r 0)).im -
      (paperQuadrilateralComplexSquare (q 1)-paperQuadrilateralComplexSquare (q 0)).im *
      (paperQuadrilateralComplexSquare (r 1)-paperQuadrilateralComplexSquare (r 0)).re ≠ 0 := by
    simpa only [f,h,Function.comp_apply,rawSquareQuarterTurn_det_sub] using hd
  have hc' : diskArcChord (paperQuadrilateralComplexSquare ∘ q) u =
      diskArcChord (paperQuadrilateralComplexSquare ∘ r) v := by
    apply rawSquareQuarterTurn_injective k
    simpa only [f,h,rawSquareQuarterTurn_diskArcChord] using hc
  obtain ⟨u',v',he⟩ := paperQuadrilateral_raw_chord_crossing_intersection q r k (paperQuadrilateralNextSide k)
    _ _ (paperQuadrilateralNextSide_ne k).symm hmn hq0side hq1side hr0side hr1side
    (fun z hz0 hz1 => paperAxisArcFromTag_strict g hg a ha s z hz0 hz1)
    (fun z hz0 hz1 => paperAxisArcFromTag_strict g hg a ha t z hz0 hz1)
    hd' u v hu0 hu1 hv0 hv1 hc'
  exact paperAxisArcFromTag_points_ne g hg a ha hproject s t hindices u' v' he

end Markov
