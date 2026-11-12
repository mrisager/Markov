import Markov.RawSquareArcCrossing

/-! Literal top-right corner cap geometry. The actual affine cap signs
construct actual transverse chord parameters; actual RAW-square topology then
forces actual Q-arc intersection. No boundary order or crossing field is used. -/

noncomputable section
open Set
namespace Markov

/-- The literal affine functional cutting off the top-right corner above the
chord joining(a,1) to(1,b). -/
def rawSquareCorner01Cap (a b : ℝ) (z : ℂ) : ℝ :=
  (1-b)*(z.re-a)+(1-a)*(z.im-1)

/-- Positive-to-negative actual cap signs construct actual transverse interior
chord data. The explicit open-square chord inequalities are pure coordinate
data; the actual Q application below derives them from different-side endpoints. -/
theorem rawSquareCorner01Chord_data
    (f g : unitInterval → ℂ)
    (hf0 : (f 0).im=1) (hf1 : (f 1).re=1)
    (ha : -1<(f 0).re ∧ (f 0).re<1) (hb : -1<(f 1).im ∧ (f 1).im<1)
    (hpos : 0<rawSquareCorner01Cap (f 0).re (f 1).im (g 0))
    (hneg : rawSquareCorner01Cap (f 0).re (f 1).im (g 1)<0)
    (hgch : ∀ t : unitInterval, 0<(t:ℝ) → (t:ℝ)<1 →
      (-1<(diskArcChord g t).re ∧ (diskArcChord g t).re<1) ∧
        (-1<(diskArcChord g t).im ∧ (diskArcChord g t).im<1)) :
    ∃ u v : unitInterval, 0<(u:ℝ) ∧ (u:ℝ)<1 ∧ 0<(v:ℝ) ∧ (v:ℝ)<1 ∧
      (f 1-f 0).re*(g 1-g 0).im-(f 1-f 0).im*(g 1-g 0).re≠0 ∧
      diskArcChord f u=diskArcChord g v := by
  let a := (f 0).re
  let b := (f 1).im
  let C0 := rawSquareCorner01Cap a b (g 0)
  let C1 := rawSquareCorner01Cap a b (g 1)
  let D := C0-C1
  have hC0 : 0<C0 := hpos
  have hC1 : C1<0 := hneg
  have hD : 0<D := by dsimp only [D]; linarith
  let v : unitInterval := ⟨C0/D,⟨(div_pos hC0 hD).le,(div_le_iff₀ hD).mpr (by dsimp only [D]; linarith)⟩⟩
  have hv0 : 0<(v:ℝ) := div_pos hC0 hD
  have hv1 : (v:ℝ)<1 := (div_lt_iff₀ hD).mpr (by dsimp only [D]; linarith)
  let w := diskArcChord g v
  have hw : (-1<w.re ∧ w.re<1) ∧ (-1<w.im ∧ w.im<1) := hgch v hv0 hv1
  have hcw : rawSquareCorner01Cap a b w=0 := by
    simp [w,diskArcChord,rawSquareCorner01Cap,v]
    field_simp [ne_of_gt hD]
    dsimp only [D,C0,C1,rawSquareCorner01Cap,a,b]
    ring
  have hr : 0<1-a := sub_pos.mpr ha.2
  have hs : 0<1-b := sub_pos.mpr hb.2
  have hnum : 0<1-w.im := sub_pos.mpr hw.2.2
  have hnumlt : 1-w.im<1-b := by
    by_contra hnot
    have hle : 1-b≤1-w.im := le_of_not_gt hnot
    have hp := mul_pos hs (sub_pos.mpr hw.1.2)
    have hn := mul_nonneg hr.le (sub_nonneg.mpr hle)
    dsimp only [rawSquareCorner01Cap] at hcw
    nlinarith
  let u : unitInterval := ⟨(1-w.im)/(1-b),
    ⟨(div_pos hnum hs).le,(div_le_iff₀ hs).mpr (by linarith)⟩⟩
  have hu0 : 0<(u:ℝ) := div_pos hnum hs
  have hu1 : (u:ℝ)<1 := (div_lt_iff₀ hs).mpr (by linarith)
  have hdet : (f 1-f 0).re*(g 1-g 0).im-(f 1-f 0).im*(g 1-g 0).re=C1-C0 := by
    simp only [Complex.sub_re,Complex.sub_im,hf0,hf1]
    dsimp only [C0,C1,rawSquareCorner01Cap,a,b]
    ring
  refine ⟨u,v,hu0,hu1,hv0,hv1,?_,?_⟩
  · rw [hdet]
    intro hzero
    linarith
  · change diskArcChord f u=w
    apply Complex.ext
    · simp only [diskArcChord,Complex.add_re,Complex.smul_re,smul_eq_mul,hf1]
      change (1-(1-w.im)/(1-b))*a+((1-w.im)/(1-b))*1=w.re
      field_simp [ne_of_gt hs]
      dsimp only [rawSquareCorner01Cap] at hcw
      nlinarith
    · simp only [diskArcChord,Complex.add_im,Complex.smul_im,smul_eq_mul,hf0]
      change (1-(1-w.im)/(1-b))*1+((1-w.im)/(1-b))*b=w.im
      field_simp [ne_of_gt hs]
      ring

/-- Any actual proper Q-arc whose source is in the positive top-right cap and
whose target is in the negative cap intersects the actual TOP-to-RIGHT arc.
Different-side chord interiors and all crossing data are constructed. -/
theorem paperQuadrilateral_corner01_cap_arcs_intersect
    (q r : C(unitInterval,paperIdealQuadrilateral))
    (hq0 : (q 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 0)
    (hq1 : (q 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 1)
    (m n : Fin 4) (hmn : m≠n)
    (hr0 : (r 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide m)
    (hr1 : (r 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide n)
    (hq : ∀ s : unitInterval, 0<(s:ℝ) → (s:ℝ)<1 → (q s:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion)
    (hr : ∀ s : unitInterval, 0<(s:ℝ) → (s:ℝ)<1 → (r s:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion)
    (hpos : 0<rawSquareCorner01Cap (paperQuadrilateralComplexSquare (q 0)).re
      (paperQuadrilateralComplexSquare (q 1)).im (paperQuadrilateralComplexSquare (r 0)))
    (hneg : rawSquareCorner01Cap (paperQuadrilateralComplexSquare (q 0)).re
      (paperQuadrilateralComplexSquare (q 1)).im (paperQuadrilateralComplexSquare (r 1))<0) :
    ∃ s t : unitInterval, q s=r t := by
  have hq0' : (paperQuadrilateralComplexSquare (q 0)).im=1 := (paperSquareChartB_eq_one_iff _).mpr hq0
  have hq1' : (paperQuadrilateralComplexSquare (q 1)).re=1 := (paperSquareChartA_eq_one_iff _).mpr hq1
  have ha := paperPuncturedSquare_horizontal_param (paperQuadrilateralToSquare (q 0)) (Or.inl hq0')
  have hb := paperPuncturedSquare_vertical_param (paperQuadrilateralToSquare (q 1)) (Or.inl hq1')
  obtain ⟨u,v,hu0,hu1,hv0,hv1,hd,hc⟩ := rawSquareCorner01Chord_data
    (paperQuadrilateralComplexSquare ∘ q) (paperQuadrilateralComplexSquare ∘ r) hq0' hq1' ha hb
    hpos hneg (paperQuadrilateral_raw_chord_strict_coordinates r m n hmn hr0 hr1)
  exact paperQuadrilateral_raw_chord_crossing_intersection q r 0 1 m n (by decide) hmn
    hq0 hq1 hr0 hr1 hq hr hd u v hu0 hu1 hv0 hv1 hc

/-- In the bounded shared-TOP/two-RIGHT case, the reversed literal endpoint
order itself constructs the cap signs and forces actual Q-arc intersection. -/
theorem paperQuadrilateral_corner01_reversed_right_order_intersect
    (q r : C(unitInterval,paperIdealQuadrilateral))
    (hq0 : (q 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 0)
    (hq1 : (q 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 1)
    (hr0 : (r 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 0)
    (hr1 : (r 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide 1)
    (hq : ∀ s : unitInterval, 0<(s:ℝ) → (s:ℝ)<1 → (q s:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion)
    (hr : ∀ s : unitInterval, 0<(s:ℝ) → (s:ℝ)<1 → (r s:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion)
    (hx : (paperQuadrilateralComplexSquare (q 0)).re<(paperQuadrilateralComplexSquare (r 0)).re)
    (hy : (paperQuadrilateralComplexSquare (r 1)).im<(paperQuadrilateralComplexSquare (q 1)).im) :
    ∃ s t : unitInterval, q s=r t := by
  have hq0' : (paperQuadrilateralComplexSquare (q 0)).im=1 := (paperSquareChartB_eq_one_iff _).mpr hq0
  have hq1' : (paperQuadrilateralComplexSquare (q 1)).re=1 := (paperSquareChartA_eq_one_iff _).mpr hq1
  have hr0' : (paperQuadrilateralComplexSquare (r 0)).im=1 := (paperSquareChartB_eq_one_iff _).mpr hr0
  have hr1' : (paperQuadrilateralComplexSquare (r 1)).re=1 := (paperSquareChartA_eq_one_iff _).mpr hr1
  have ha := paperPuncturedSquare_horizontal_param (paperQuadrilateralToSquare (q 0)) (Or.inl hq0')
  have hb := paperPuncturedSquare_vertical_param (paperQuadrilateralToSquare (q 1)) (Or.inl hq1')
  apply paperQuadrilateral_corner01_cap_arcs_intersect q r hq0 hq1 0 1 (by decide) hr0 hr1 hq hr
  · simpa only [rawSquareCorner01Cap,hr0',sub_self,mul_zero,add_zero] using
      mul_pos (sub_pos.mpr hb.2) (sub_pos.mpr hx)
  · have hapos : 0<1-(paperQuadrilateralComplexSquare (q 0)).re := sub_pos.mpr ha.2
    have hp := mul_neg_of_pos_of_neg hapos (sub_neg.mpr hy)
    dsimp only [rawSquareCorner01Cap]
    rw [hr1']
    nlinarith

end Markov
