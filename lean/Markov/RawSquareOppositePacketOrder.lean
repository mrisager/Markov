import Markov.RawSquareArcCrossing
import Markov.PaperQuadrilateralRawSideFrame
import Markov.PaperAxisTaggedOrientedArcs

/-! Actual same-opposite-packet order. Reversed TOP-to-BOTTOM endpoint
matching constructs a strictly interior transverse chord intersection. Literal
quarter turns transport the data back to the original Q arcs. Actual full
family separation then proves partner order, rather than assuming it. -/

noncomputable section
open Set
namespace Markov

/-- Two TOP-to-BOTTOM chords with reversed endpoint order intersect at the
same explicit strictly interior parameter. No crossing witness is supplied. -/
theorem rawSquareTopBottomReversedChord_data
    (f g : unitInterval → ℂ)
    (hf0 : (f 0).im=1) (hf1 : (f 1).im= -1)
    (hg0 : (g 0).im=1) (hg1 : (g 1).im= -1)
    (hx : (f 0).re<(g 0).re) (hy : (g 1).re<(f 1).re) :
    ∃ u v : unitInterval, 0<(u:ℝ) ∧ (u:ℝ)<1 ∧ 0<(v:ℝ) ∧ (v:ℝ)<1 ∧
      (f 1-f 0).re*(g 1-g 0).im-(f 1-f 0).im*(g 1-g 0).re≠0 ∧
      diskArcChord f u=diskArcChord g v := by
  let U := (g 0).re-(f 0).re
  let V := (f 1).re-(g 1).re
  let D := U+V
  have hU : 0<U := sub_pos.mpr hx
  have hV : 0<V := sub_pos.mpr hy
  have hD : 0<D := add_pos hU hV
  let t : unitInterval := ⟨U/D,⟨(div_pos hU hD).le,
    (div_le_iff₀ hD).mpr (by dsimp only [D]; linarith)⟩⟩
  have ht0 : 0<(t:ℝ) := div_pos hU hD
  have ht1 : (t:ℝ)<1 := (div_lt_iff₀ hD).mpr (by dsimp only [D]; linarith)
  refine ⟨t,t,ht0,ht1,ht0,ht1,?_,?_⟩
  · simp only [Complex.sub_re,Complex.sub_im,hf0,hf1,hg0,hg1]
    intro heq
    dsimp only [D,U,V] at hD
    nlinarith
  · apply Complex.ext
    · simp [diskArcChord,t]
      field_simp [ne_of_gt hD]
      dsimp only [D,U,V]
      ring
    · simp [diskArcChord,hf0,hf1,hg0,hg1]

/-- Actual proper TOP-to-BOTTOM Q arcs with reversed literal free-coordinate
matching must intersect. The crossing and strict chord interiors are proved
from the actual coordinate and side data. -/
theorem paperQuadrilateral_top_bottom_reversed_order_intersect
    (q r : C(unitInterval,paperIdealQuadrilateral))
    (hq0 : (q 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 0)
    (hq1 : (q 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 2)
    (hr0 : (r 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 0)
    (hr1 : (r 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 2)
    (hq : ∀ s : unitInterval, 0<(s:ℝ) → (s:ℝ)<1 →
      (q s:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion)
    (hr : ∀ s : unitInterval, 0<(s:ℝ) → (s:ℝ)<1 →
      (r s:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion)
    (hx : (paperQuadrilateralComplexSquare (q 0)).re<
      (paperQuadrilateralComplexSquare (r 0)).re)
    (hy : (paperQuadrilateralComplexSquare (r 1)).re<
      (paperQuadrilateralComplexSquare (q 1)).re) :
    ∃ s t : unitInterval, q s=r t := by
  have hq0' : (paperQuadrilateralComplexSquare (q 0)).im=1 :=
    (paperSquareChartB_eq_one_iff _).mpr hq0
  have hq1' : (paperQuadrilateralComplexSquare (q 1)).im= -1 :=
    (paperSquareChartB_eq_neg_one_iff _).mpr hq1
  have hr0' : (paperQuadrilateralComplexSquare (r 0)).im=1 :=
    (paperSquareChartB_eq_one_iff _).mpr hr0
  have hr1' : (paperQuadrilateralComplexSquare (r 1)).im= -1 :=
    (paperSquareChartB_eq_neg_one_iff _).mpr hr1
  obtain ⟨u,v,hu0,hu1,hv0,hv1,hd,hc⟩ := rawSquareTopBottomReversedChord_data
    (paperQuadrilateralComplexSquare ∘ q) (paperQuadrilateralComplexSquare ∘ r)
    hq0' hq1' hr0' hr1' hx hy
  exact paperQuadrilateral_raw_chord_crossing_intersection q r 0 2 0 2
    (by decide) (by decide) hq0 hq1 hr0 hr1 hq hr hd u v hu0 hu1 hv0 hv1 hc

/-- In the literal selected-side frame, the actual opposite side is BOTTOM;
its frame free coordinate is minus its clockwise boundary coordinate. -/
theorem paperQuadrilateralRawSideFrame_opposite (k : Fin 4)
    (z : paperIdealQuadrilateral)
    (hz : z.val∈paperQuadrilateralGeodesicSide (paperQuadrilateralOppositeSide k)) :
    (paperQuadrilateralRawSideFrame k z).im= -1 ∧
      (paperQuadrilateralRawSideFrame k z).re=
        -paperQuadrilateralRawBoundarySideCoordinate (paperQuadrilateralOppositeSide k) z := by
  refine ⟨?_,?_⟩
  · have h := (paperQuadrilateralRawSideFrame_side_iff k (paperQuadrilateralOppositeSide k) z).mpr hz
    fin_cases k <;> simpa [paperQuadrilateralOppositeSide] using h
  · fin_cases k <;>
      simp [paperQuadrilateralRawSideFrame,rawSquareQuarterTurn,
        paperQuadrilateralOppositeSide,paperQuadrilateralComplexSquare,
        paperQuadrilateralRawBoundarySideCoordinate,Complex.mul_re]

/-- The reversed-order obstruction for EVERY literal opposite-side packet.
The actual rotated chord data is transported back before topology is applied
to the original Q arcs; no surface rotation is assumed. -/
theorem paperQuadrilateral_opposite_reversed_frame_order_intersect
    (k : Fin 4) (q r : C(unitInterval,paperIdealQuadrilateral))
    (hq0 : (q 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide k)
    (hq1 : (q 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide (paperQuadrilateralOppositeSide k))
    (hr0 : (r 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide k)
    (hr1 : (r 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide (paperQuadrilateralOppositeSide k))
    (hq : ∀ s : unitInterval, 0<(s:ℝ) → (s:ℝ)<1 →
      (q s:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion)
    (hr : ∀ s : unitInterval, 0<(s:ℝ) → (s:ℝ)<1 →
      (r s:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion)
    (hx : (paperQuadrilateralRawSideFrame k (q 0)).re<
      (paperQuadrilateralRawSideFrame k (r 0)).re)
    (hy : (paperQuadrilateralRawSideFrame k (r 1)).re<
      (paperQuadrilateralRawSideFrame k (q 1)).re) :
    ∃ s t : unitInterval, q s=r t := by
  let f : unitInterval → ℂ := rawSquareQuarterTurn k ∘ (paperQuadrilateralComplexSquare ∘ q)
  let h : unitInterval → ℂ := rawSquareQuarterTurn k ∘ (paperQuadrilateralComplexSquare ∘ r)
  have hf0 : (f 0).im=1 := (paperQuadrilateralRawSideFrame_top k (q 0) hq0).1
  have hf1 : (f 1).im= -1 := (paperQuadrilateralRawSideFrame_opposite k (q 1) hq1).1
  have hh0 : (h 0).im=1 := (paperQuadrilateralRawSideFrame_top k (r 0) hr0).1
  have hh1 : (h 1).im= -1 := (paperQuadrilateralRawSideFrame_opposite k (r 1) hr1).1
  obtain ⟨u,v,hu0,hu1,hv0,hv1,hd,hc⟩ := rawSquareTopBottomReversedChord_data
    f h hf0 hf1 hh0 hh1 hx hy
  have hd' : (paperQuadrilateralComplexSquare (q 1)-paperQuadrilateralComplexSquare (q 0)).re *
      (paperQuadrilateralComplexSquare (r 1)-paperQuadrilateralComplexSquare (r 0)).im -
      (paperQuadrilateralComplexSquare (q 1)-paperQuadrilateralComplexSquare (q 0)).im *
      (paperQuadrilateralComplexSquare (r 1)-paperQuadrilateralComplexSquare (r 0)).re≠0 := by
    simpa only [f,h,Function.comp_apply,rawSquareQuarterTurn_det_sub] using hd
  have hc' : diskArcChord (paperQuadrilateralComplexSquare ∘ q) u=
      diskArcChord (paperQuadrilateralComplexSquare ∘ r) v := by
    apply rawSquareQuarterTurn_injective k
    simpa only [f,h,rawSquareQuarterTurn_diskArcChord] using hc
  have hko : k≠paperQuadrilateralOppositeSide k := by fin_cases k <;> decide
  exact paperQuadrilateral_raw_chord_crossing_intersection q r k (paperQuadrilateralOppositeSide k)
    k (paperQuadrilateralOppositeSide k) hko hko hq0 hq1 hr0 hr1 hq hr
    hd' u v hu0 hu1 hv0 hv1 hc'

/-- For actually disjoint proper arcs in one opposite-side packet, increasing
clockwise source coordinates force nonincreasing clockwise partner coordinates. -/
theorem paperQuadrilateral_opposite_raw_partner_antitone
    (k : Fin 4) (q r : C(unitInterval,paperIdealQuadrilateral))
    (hq0 : (q 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide k)
    (hq1 : (q 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide (paperQuadrilateralOppositeSide k))
    (hr0 : (r 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide k)
    (hr1 : (r 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide (paperQuadrilateralOppositeSide k))
    (hq : ∀ s : unitInterval, 0<(s:ℝ) → (s:ℝ)<1 →
      (q s:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion)
    (hr : ∀ s : unitInterval, 0<(s:ℝ) → (s:ℝ)<1 →
      (r s:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion)
    (hdisjoint : ∀ s t : unitInterval, q s≠r t)
    (hx : paperQuadrilateralRawBoundarySideCoordinate k (q 0)<
      paperQuadrilateralRawBoundarySideCoordinate k (r 0)) :
    paperQuadrilateralRawBoundarySideCoordinate (paperQuadrilateralOppositeSide k) (r 1)≤
      paperQuadrilateralRawBoundarySideCoordinate (paperQuadrilateralOppositeSide k) (q 1) := by
  have hx' : (paperQuadrilateralRawSideFrame k (q 0)).re<
      (paperQuadrilateralRawSideFrame k (r 0)).re := by
    simpa only [paperQuadrilateralRawSideFrame_re] using hx
  have hle : (paperQuadrilateralRawSideFrame k (q 1)).re≤
      (paperQuadrilateralRawSideFrame k (r 1)).re := by
    by_contra hn
    obtain ⟨s,t,he⟩ := paperQuadrilateral_opposite_reversed_frame_order_intersect
      k q r hq0 hq1 hr0 hr1 hq hr hx' (lt_of_not_ge hn)
    exact hdisjoint s t he
  rw [(paperQuadrilateralRawSideFrame_opposite k (q 1) hq1).2,
    (paperQuadrilateralRawSideFrame_opposite k (r 1) hr1).2] at hle
  linarith

end Markov
