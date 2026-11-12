import Markov.ConvexFrontierLoopObstruction
import Markov.DiskArcChordHomotopy
import Markov.PaperQuadrilateralSideAdjacency
import Markov.PaperQuadrilateralDiskChart
import Markov.PaperQuadrilateralSquareEdges
import Markov.DiskChordEndpointDistinct
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Generic actual RAW-square proper-Q arc crossing. All topology is derived
from the checked actual convex-frontier obstruction. -/

noncomputable section
open Set Topology Metric
namespace Markov

private def parameterRect (u v : ℝ) : Set ℂ :=
  Icc (-u) (1-u) ×ℂ Icc (-v) (1-v)

private theorem rect_convex (u v : ℝ) : Convex ℝ (parameterRect u v) := by
  change Convex ℝ (Complex.equivRealProdLm ⁻¹' (Icc (-u) (1-u) ×ˢ Icc (-v) (1-v)))
  exact ((convex_Icc (-u) (1-u)).prod (convex_Icc (-v) (1-v))).linear_preimage
    Complex.equivRealProdLm.toLinearMap

private theorem rect_closed (u v : ℝ) : IsClosed (parameterRect u v) :=
  isClosed_Icc.reProdIm isClosed_Icc

private theorem rect_bounded (u v : ℝ) : Bornology.IsBounded (parameterRect u v) :=
  (isBounded_Icc (-u) (1-u)).reProdIm (isBounded_Icc (-v) (1-v))

private theorem rect_nhds (u v : ℝ) (hu0 : 0 < u) (hu1 : u < 1)
    (hv0 : 0 < v) (hv1 : v < 1) : parameterRect u v ∈ 𝓝 0 := by
  apply mem_interior_iff_mem_nhds.mp
  rw [parameterRect, Complex.interior_reProdIm, interior_Icc, interior_Icc]
  exact ⟨⟨by simpa using neg_neg_of_pos hu0, by simpa using sub_pos.mpr hu1⟩,
    ⟨by simpa using neg_neg_of_pos hv0, by simpa using sub_pos.mpr hv1⟩⟩

private def rectFirst (u v : ℝ) (z : ↥(closure (parameterRect u v))) : unitInterval :=
  ⟨z.val.re+u, by
    have hz : z.val ∈ parameterRect u v := by simpa only [(rect_closed u v).closure_eq] using z.property
    exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩⟩

private def rectSecond (u v : ℝ) (z : ↥(closure (parameterRect u v))) : unitInterval :=
  ⟨z.val.im+v, by
    have hz : z.val ∈ parameterRect u v := by simpa only [(rect_closed u v).closure_eq] using z.property
    exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩

@[fun_prop] private theorem rectFirst_continuous (u v : ℝ) : Continuous (rectFirst u v) := by
  apply Continuous.subtype_mk
  change Continuous (fun z : ↥(closure (parameterRect u v)) => z.val.re+u)
  fun_prop

@[fun_prop] private theorem rectSecond_continuous (u v : ℝ) : Continuous (rectSecond u v) := by
  apply Continuous.subtype_mk
  change Continuous (fun z : ↥(closure (parameterRect u v)) => z.val.im+v)
  fun_prop

private theorem interval_strict (t : unitInterval) (ht : ¬(t=0 ∨ t=1)) :
    0 < (t : ℝ) ∧ (t : ℝ) < 1 := by
  have h0 : (t : ℝ) ≠ 0 := fun h => ht (Or.inl (Subtype.ext h))
  have h1 : (t : ℝ) ≠ 1 := fun h => ht (Or.inr (Subtype.ext h))
  exact ⟨lt_of_le_of_ne t.property.1 h0.symm, lt_of_le_of_ne t.property.2 h1⟩

private theorem rect_boundary (u v : ℝ) (z : ↥(frontier (parameterRect u v))) :
    let zc : ↥(closure (parameterRect u v)) := ⟨z.val, frontier_subset_closure z.property⟩
    (rectFirst u v zc=0 ∨ rectFirst u v zc=1) ∨
      (rectSecond u v zc=0 ∨ rectSecond u v zc=1) := by
  dsimp only
  by_cases ht : rectFirst u v ⟨z.val, frontier_subset_closure z.property⟩=0 ∨
      rectFirst u v ⟨z.val, frontier_subset_closure z.property⟩=1
  · exact Or.inl ht
  by_cases hs : rectSecond u v ⟨z.val, frontier_subset_closure z.property⟩=0 ∨
      rectSecond u v ⟨z.val, frontier_subset_closure z.property⟩=1
  · exact Or.inr hs
  obtain ⟨ht0, ht1⟩ := interval_strict _ ht
  obtain ⟨hs0, hs1⟩ := interval_strict _ hs
  exfalso
  apply z.property.2
  change z.val ∈ interior (Icc (-u) (1-u) ×ℂ Icc (-v) (1-v))
  rw [Complex.interior_reProdIm, interior_Icc, interior_Icc]
  change 0 < z.val.re+u at ht0
  change z.val.re+u < 1 at ht1
  change 0 < z.val.im+v at hs0
  change z.val.im+v < 1 at hs1
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

private def rectCorner (u v : ℝ) : ↥(frontier (parameterRect u v)) :=
  ⟨⟨-u,-v⟩, by
    constructor
    · apply subset_closure
      exact ⟨⟨le_rfl, by linarith⟩, ⟨le_rfl, by linarith⟩⟩
    · rw [parameterRect, Complex.interior_reProdIm, interior_Icc, interior_Icc]
      intro h
      exact (lt_irrefl (-u)) h.1.1⟩

private theorem rectCorner_first (u v : ℝ) :
    rectFirst u v ⟨(rectCorner u v).val, frontier_subset_closure (rectCorner u v).property⟩ = 0 := by
  apply Subtype.ext
  simp [rectFirst, rectCorner]

private theorem rectCorner_second (u v : ℝ) :
    rectSecond u v ⟨(rectCorner u v).val, frontier_subset_closure (rectCorner u v).property⟩ = 0 := by
  apply Subtype.ext
  simp [rectSecond, rectCorner]

private def chordLinearMap (A B : ℂ) : ℂ →ₗ[ℝ] ℂ where
  toFun z := z.re • A - z.im • B
  map_add' z w := by simp only [Complex.add_re, Complex.add_im, add_smul]; module
  map_smul' r z := by simp [smul_sub, mul_comm]; ring

private theorem chordLinearMap_injective (A B : ℂ)
    (hd : A.re*B.im-A.im*B.re ≠ 0) : Function.Injective (chordLinearMap A B) := by
  intro z w h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [chordLinearMap] at hr hi
  have hre : (z.re-w.re)*(A.re*B.im-A.im*B.re)=0 := by
    linear_combination B.im*hr - B.re*hi
  have him : (z.im-w.im)*(A.re*B.im-A.im*B.re)=0 := by
    linear_combination A.im*hr - A.re*hi
  exact Complex.ext (sub_eq_zero.mp ((mul_eq_zero.mp hre).resolve_right hd))
    (sub_eq_zero.mp ((mul_eq_zero.mp him).resolve_right hd))

private def chordLinearEquiv (A B : ℂ) (hd : A.re*B.im-A.im*B.re ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  (LinearEquiv.ofInjectiveEndo (chordLinearMap A B) (chordLinearMap_injective A B hd)).toContinuousLinearEquiv

private theorem chord_diff_rect (f g : unitInterval → ℂ) (u v : unitInterval)
    (hr : diskArcChord f u = diskArcChord g v)
    (z : ↥(closure (parameterRect (u : ℝ) (v : ℝ)))) :
    diskArcChord f (rectFirst u v z) - diskArcChord g (rectSecond u v z) =
      chordLinearMap (f 1-f 0) (g 1-g 0) z.val := by
  apply Complex.ext
  · have hx := congrArg Complex.re hr
    simp [diskArcChord, rectFirst, rectSecond, chordLinearMap] at hx ⊢
    nlinarith [hx]
  · have hx := congrArg Complex.im hr
    simp [diskArcChord, rectFirst, rectSecond, chordLinearMap] at hx ⊢
    nlinarith [hx]

private def rawSquareOpen : Set ℂ := Ioo (-1) 1 ×ℂ Ioo (-1) 1
private def rawSquareBoundary (z : ℂ) : Prop := z.re=1 ∨ z.re= -1 ∨ z.im=1 ∨ z.im= -1

private theorem rawSquareOpen_convex : Convex ℝ rawSquareOpen := by
  change Convex ℝ (Complex.equivRealProdLm ⁻¹' (Ioo (-1) 1 ×ˢ Ioo (-1) 1))
  exact ((convex_Ioo (-1) 1).prod (convex_Ioo (-1) 1)).linear_preimage
    Complex.equivRealProdLm.toLinearMap

private theorem rawSquareBoundary_ne_open {z w : ℂ}
    (hz : rawSquareBoundary z) (hw : w∈rawSquareOpen) : z≠w := by
  intro heq
  subst w
  change (-1<z.re ∧ z.re<1) ∧ (-1<z.im ∧ z.im<1) at hw
  rcases hz with h | h | h | h <;> linarith [hw.1.1,hw.1.2,hw.2.1,hw.2.2]

private theorem rawSquareHomotopy_open
    (f : unitInterval → ℂ)
    (hfi : ∀ t : unitInterval, 0<(t:ℝ) → (t:ℝ)<1 → f t∈rawSquareOpen)
    (hfch : ∀ t : unitInterval, 0<(t:ℝ) → (t:ℝ)<1 → diskArcChord f t∈rawSquareOpen)
    (s t : unitInterval) (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) :
    diskArcChordHomotopy f s t∈rawSquareOpen :=
  rawSquareOpen_convex (hfi t ht0 ht1) (hfch t ht0 ht1)
    (sub_nonneg.mpr s.property.2) s.property.1 (by ring)

private theorem rawSquareHomotopy_boundary_ne
    (f g : unitInterval → ℂ)
    (hfB : ∀ t : unitInterval, (t=0 ∨ t=1) → rawSquareBoundary (f t))
    (hgB : ∀ t : unitInterval, (t=0 ∨ t=1) → rawSquareBoundary (g t))
    (hfi : ∀ t : unitInterval, 0<(t:ℝ) → (t:ℝ)<1 → f t∈rawSquareOpen)
    (hgi : ∀ t : unitInterval, 0<(t:ℝ) → (t:ℝ)<1 → g t∈rawSquareOpen)
    (hfch : ∀ t : unitInterval, 0<(t:ℝ) → (t:ℝ)<1 → diskArcChord f t∈rawSquareOpen)
    (hgch : ∀ t : unitInterval, 0<(t:ℝ) → (t:ℝ)<1 → diskArcChord g t∈rawSquareOpen)
    (hend : ∀ t u : unitInterval, (t=0 ∨ t=1) → (u=0 ∨ u=1) → f t≠g u)
    (s t u : unitInterval) (hb : (t=0 ∨ t=1) ∨ (u=0 ∨ u=1)) :
    diskArcChordHomotopy f s t ≠ diskArcChordHomotopy g s u := by
  by_cases ht : t=0 ∨ t=1
  · rw [diskArcChordHomotopy_fixed_endpoints f s t ht]
    by_cases hu : u=0 ∨ u=1
    · rw [diskArcChordHomotopy_fixed_endpoints g s u hu]
      exact hend t u ht hu
    · obtain ⟨hu0,hu1⟩ := interval_strict u hu
      exact rawSquareBoundary_ne_open (hfB t ht) (rawSquareHomotopy_open g hgi hgch s u hu0 hu1)
  · have hu := hb.resolve_left ht
    rw [diskArcChordHomotopy_fixed_endpoints g s u hu]
    obtain ⟨ht0,ht1⟩ := interval_strict t ht
    exact (rawSquareBoundary_ne_open (hgB u hu) (rawSquareHomotopy_open f hfi hfch s t ht0 ht1)).symm

/-- Actual open-square boundary obstruction with actual chord data. -/
private theorem rawSquareArcs_intersect_of_transverse_interior_chords
    (f g : unitInterval → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfB : ∀ t : unitInterval, (t=0 ∨ t=1) → rawSquareBoundary (f t))
    (hgB : ∀ t : unitInterval, (t=0 ∨ t=1) → rawSquareBoundary (g t))
    (hfi : ∀ t : unitInterval, 0<(t:ℝ) → (t:ℝ)<1 → f t∈rawSquareOpen)
    (hgi : ∀ t : unitInterval, 0<(t:ℝ) → (t:ℝ)<1 → g t∈rawSquareOpen)
    (hfch : ∀ t : unitInterval, 0<(t:ℝ) → (t:ℝ)<1 → diskArcChord f t∈rawSquareOpen)
    (hgch : ∀ t : unitInterval, 0<(t:ℝ) → (t:ℝ)<1 → diskArcChord g t∈rawSquareOpen)
    (hend : ∀ t s : unitInterval, (t=0 ∨ t=1) → (s=0 ∨ s=1) → f t ≠ g s)
    (hd : (f 1-f 0).re*(g 1-g 0).im-(f 1-f 0).im*(g 1-g 0).re ≠ 0)
    (u v : unitInterval) (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1)
    (hv0 : 0 < (v : ℝ)) (hv1 : (v : ℝ) < 1)
    (hr : diskArcChord f u = diskArcChord g v) :
    ∃ t s : unitInterval, f t = g s := by
  let P := parameterRect (u : ℝ) (v : ℝ)
  let E := chordLinearEquiv (f 1-f 0) (g 1-g 0) hd
  let F : ↥(closure P) → ℂ := fun z => E.symm (f (rectFirst u v z)-g (rectSecond u v z))
  let H : unitInterval × ↥(frontier P) → ℂ := fun sz =>
    let z : ↥(closure P) := ⟨sz.2.val, frontier_subset_closure sz.2.property⟩
    E.symm (diskArcChordHomotopy f sz.1 (rectFirst u v z)-
      diskArcChordHomotopy g sz.1 (rectSecond u v z))
  have hFc : Continuous F := by
    exact E.symm.continuous.comp ((hf.comp (rectFirst_continuous u v)).sub
      (hg.comp (rectSecond_continuous u v)))
  have hHc : Continuous H := by
    dsimp [H]
    apply E.symm.continuous.comp
    dsimp [diskArcChordHomotopy, diskArcChord]
    fun_prop
  have hH0 : ∀ z : ↥(frontier P), H (0,z)=F ⟨z.val, frontier_subset_closure z.property⟩ := by
    intro z
    simp [H,F,diskArcChordHomotopy]
  have hH1 : ∀ z : ↥(frontier P), H (1,z)=z.val := by
    intro z
    dsimp [H]
    simp only [diskArcChordHomotopy, show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self, zero_smul, one_smul, zero_add]
    rw [chord_diff_rect f g u v hr]
    exact E.symm_apply_apply z.val
  have hHb : ∀ s : unitInterval, H (s,rectCorner u v)=(rectCorner u v).val := by
    intro s
    dsimp [H]
    rw [rectCorner_first, rectCorner_second,
      diskArcChordHomotopy_fixed_endpoints f s 0 (Or.inl rfl),
      diskArcChordHomotopy_fixed_endpoints g s 0 (Or.inl rfl)]
    have he := chord_diff_rect f g u v hr
      ⟨(rectCorner u v).val, frontier_subset_closure (rectCorner u v).property⟩
    rw [rectCorner_first, rectCorner_second] at he
    simp only [diskArcChord, show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, one_smul, zero_smul, add_zero] at he
    rw [he]
    exact E.symm_apply_apply _
  have hHn : ∀ sz : unitInterval × ↥(frontier P), H sz ≠ 0 := by
    intro sz he
    have hne := rawSquareHomotopy_boundary_ne f g hfB hgB hfi hgi hfch hgch hend
      sz.1 _ _ (rect_boundary u v sz.2)
    apply hne
    apply sub_eq_zero.mp
    have hzero := congrArg E he
    simpa only [H, ContinuousLinearEquiv.apply_symm_apply, map_zero] using hzero
  obtain ⟨z,hz⟩ := convexFrontier_boundary_homotopy_has_zero P (rect_convex u v)
    (rect_nhds u v hu0 hu1 hv0 hv1) (rect_bounded u v) (rectCorner u v)
    F hFc H hHc hH0 hH1 hHb hHn
  refine ⟨rectFirst u v z,rectSecond u v z,sub_eq_zero.mp ?_⟩
  have he := congrArg E hz
  simpa only [F, ContinuousLinearEquiv.apply_symm_apply, map_zero] using he

private theorem rawQ_side_unique (k l : Fin 4) (z : UpperHalfPlane)
    (hk : z∈paperQuadrilateralGeodesicSide k) (hl : z∈paperQuadrilateralGeodesicSide l) : k=l := by
  by_contra hne
  exact Set.disjoint_left.mp (paperQuadrilateralGeodesicSides_disjoint k l hne) hk hl

private theorem rawQ_boundary (z : paperIdealQuadrilateral) (k : Fin 4)
    (hz : (z:UpperHalfPlane)∈paperQuadrilateralGeodesicSide k) :
    rawSquareBoundary (paperQuadrilateralComplexSquare z) := by
  fin_cases k
  · exact Or.inr (Or.inr (Or.inl ((paperSquareChartB_eq_one_iff z).mpr hz)))
  · exact Or.inl ((paperSquareChartA_eq_one_iff z).mpr hz)
  · exact Or.inr (Or.inr (Or.inr ((paperSquareChartB_eq_neg_one_iff z).mpr hz)))
  · exact Or.inr (Or.inl ((paperSquareChartA_eq_neg_one_iff z).mpr hz))

private theorem rawQ_open (z : paperIdealQuadrilateral)
    (hz : (z:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion) :
    paperQuadrilateralComplexSquare z∈rawSquareOpen := by
  have hside (k : Fin 4) : (z:UpperHalfPlane)∉paperQuadrilateralGeodesicSide k :=
    fun hk => (paperQuadrilateralGeodesicSide_subset_frontier k hk).2
      (paperIdealQuadrilateralStrictRegion_subset_interior hz)
  have hA1 : paperSquareChartA z≠1 := fun h => hside 1 ((paperSquareChartA_eq_one_iff z).mp h)
  have hAm : paperSquareChartA z≠ -1 := fun h => hside 3 ((paperSquareChartA_eq_neg_one_iff z).mp h)
  have hB1 : paperSquareChartB z≠1 := fun h => hside 0 ((paperSquareChartB_eq_one_iff z).mp h)
  have hBm : paperSquareChartB z≠ -1 := fun h => hside 2 ((paperSquareChartB_eq_neg_one_iff z).mp h)
  have h := paperSquareChart_mem z
  obtain ⟨hAl,hAr⟩ := abs_le.mp h.1
  obtain ⟨hBl,hBr⟩ := abs_le.mp h.2.1
  exact ⟨⟨lt_of_le_of_ne hAl hAm.symm,lt_of_le_of_ne hAr hA1⟩,
    ⟨lt_of_le_of_ne hBl hBm.symm,lt_of_le_of_ne hBr hB1⟩⟩

private theorem rawScalar_combo_lt_one (x y r : ℝ) (hx : x≤1) (hy : y≤1)
    (hne : ¬(x=1 ∧ y=1)) (hr0 : 0<r) (hr1 : r<1) : (1-r)*x+r*y<1 := by
  by_cases hx1 : x=1
  · have hy1 : y<1 := lt_of_le_of_ne hy (fun h => hne ⟨hx1,h⟩)
    have hp := mul_pos hr0 (sub_pos.mpr hy1)
    have hn := mul_nonneg (sub_pos.mpr hr1).le (sub_nonneg.mpr hx)
    nlinarith
  · have hxlt : x<1 := lt_of_le_of_ne hx hx1
    have hp := mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hxlt)
    have hn := mul_nonneg hr0.le (sub_nonneg.mpr hy)
    nlinarith

private theorem rawScalar_combo_strict (x y r : ℝ)
    (hx : -1≤x ∧ x≤1) (hy : -1≤y ∧ y≤1)
    (hup : ¬(x=1 ∧ y=1)) (hlo : ¬(x= -1 ∧ y= -1)) (hr0 : 0<r) (hr1 : r<1) :
    -1<(1-r)*x+r*y ∧ (1-r)*x+r*y<1 := by
  have hn := rawScalar_combo_lt_one (-x) (-y) r (by linarith [hx.1]) (by linarith [hy.1])
    (by rintro ⟨hx',hy'⟩; apply hlo; constructor <;> linarith) hr0 hr1
  exact ⟨by nlinarith,rawScalar_combo_lt_one x y r hx.2 hy.2 hup hr0 hr1⟩

private theorem rawQ_chord_open (q : C(unitInterval,paperIdealQuadrilateral))
    (k l : Fin 4) (hkl : k≠l)
    (hq0 : (q 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide k)
    (hq1 : (q 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide l)
    (t : unitInterval) (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) :
    diskArcChord (paperQuadrilateralComplexSquare ∘ q) t∈rawSquareOpen := by
  have noCommon (e : Fin 4) (h0 : (q 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide e)
      (h1 : (q 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide e) : False :=
    hkl ((rawQ_side_unique k e _ hq0 h0).trans (rawQ_side_unique l e _ hq1 h1).symm)
  have b0 := paperSquareChart_mem (q 0)
  have b1 := paperSquareChart_mem (q 1)
  have hr := rawScalar_combo_strict (paperQuadrilateralComplexSquare (q 0)).re
    (paperQuadrilateralComplexSquare (q 1)).re (t:ℝ) (abs_le.mp b0.1) (abs_le.mp b1.1)
    (by rintro ⟨h0,h1⟩; exact noCommon 1 ((paperSquareChartA_eq_one_iff _).mp h0) ((paperSquareChartA_eq_one_iff _).mp h1))
    (by rintro ⟨h0,h1⟩; exact noCommon 3 ((paperSquareChartA_eq_neg_one_iff _).mp h0) ((paperSquareChartA_eq_neg_one_iff _).mp h1)) ht0 ht1
  have hi := rawScalar_combo_strict (paperQuadrilateralComplexSquare (q 0)).im
    (paperQuadrilateralComplexSquare (q 1)).im (t:ℝ) (abs_le.mp b0.2.1) (abs_le.mp b1.2.1)
    (by rintro ⟨h0,h1⟩; exact noCommon 0 ((paperSquareChartB_eq_one_iff _).mp h0) ((paperSquareChartB_eq_one_iff _).mp h1))
    (by rintro ⟨h0,h1⟩; exact noCommon 2 ((paperSquareChartB_eq_neg_one_iff _).mp h0) ((paperSquareChartB_eq_neg_one_iff _).mp h1)) ht0 ht1
  constructor
  · simpa [diskArcChord] using hr
  · simpa [diskArcChord] using hi

/-- Actual different-side noncorner Q endpoints have raw-square chord points
strictly in the open square at all strictly interior chord parameters. -/
theorem paperQuadrilateral_raw_chord_strict_coordinates
    (q : C(unitInterval,paperIdealQuadrilateral)) (k l : Fin 4) (hkl : k≠l)
    (hq0 : (q 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide k)
    (hq1 : (q 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide l)
    (t : unitInterval) (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) :
    (-1<(diskArcChord (paperQuadrilateralComplexSquare ∘ q) t).re ∧
      (diskArcChord (paperQuadrilateralComplexSquare ∘ q) t).re<1) ∧
      (-1<(diskArcChord (paperQuadrilateralComplexSquare ∘ q) t).im ∧
        (diskArcChord (paperQuadrilateralComplexSquare ∘ q) t).im<1) :=
  rawQ_chord_open q k l hkl hq0 hq1 t ht0 ht1

private theorem rawQ_injective : Function.Injective paperQuadrilateralComplexSquare := by
  intro z w h
  apply paperQuadrilateralSquareHomeomorph.injective
  apply Subtype.ext
  exact Prod.ext (congrArg Complex.re h) (congrArg Complex.im h)

/-- Generic actual RAW-square chord crossing implies actual proper-Q arc
intersection, including paths with endpoint sides in common. Distinct-side
endpoints give strict raw chord interiors by actual side uniqueness; the actual
convex-frontier obstruction supplies topology. Cross-endpoint distinctness is
derived from the actual transverse chord data, not assumed as an order field. -/
theorem paperQuadrilateral_raw_chord_crossing_intersection
    (q r : C(unitInterval,paperIdealQuadrilateral))
    (k l m n : Fin 4) (hkl : k≠l) (hmn : m≠n)
    (hq0 : (q 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide k)
    (hq1 : (q 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide l)
    (hr0 : (r 0:UpperHalfPlane)∈paperQuadrilateralGeodesicSide m)
    (hr1 : (r 1:UpperHalfPlane)∈paperQuadrilateralGeodesicSide n)
    (hq : ∀ s : unitInterval, 0<(s:ℝ) → (s:ℝ)<1 → (q s:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion)
    (hr : ∀ s : unitInterval, 0<(s:ℝ) → (s:ℝ)<1 → (r s:UpperHalfPlane)∈paperIdealQuadrilateralStrictRegion)
    (hd : ((paperQuadrilateralComplexSquare (q 1)-paperQuadrilateralComplexSquare (q 0)).re *
        (paperQuadrilateralComplexSquare (r 1)-paperQuadrilateralComplexSquare (r 0)).im -
      (paperQuadrilateralComplexSquare (q 1)-paperQuadrilateralComplexSquare (q 0)).im *
        (paperQuadrilateralComplexSquare (r 1)-paperQuadrilateralComplexSquare (r 0)).re)≠0)
    (u v : unitInterval) (hu0 : 0<(u:ℝ)) (hu1 : (u:ℝ)<1) (hv0 : 0<(v:ℝ)) (hv1 : (v:ℝ)<1)
    (hc : diskArcChord (paperQuadrilateralComplexSquare ∘ q) u =
      diskArcChord (paperQuadrilateralComplexSquare ∘ r) v) :
    ∃ s t : unitInterval, q s=r t := by
  have hend := diskArcChord_cross_endpoints_ne_of_transverse_interior_intersection
    (paperQuadrilateralComplexSquare ∘ q) (paperQuadrilateralComplexSquare ∘ r) hd u v hu0 hu1 hc
  obtain ⟨s,t,hst⟩ := rawSquareArcs_intersect_of_transverse_interior_chords
    (paperQuadrilateralComplexSquare ∘ q) (paperQuadrilateralComplexSquare ∘ r)
    (continuous_paperQuadrilateralComplexSquare.comp q.continuous)
    (continuous_paperQuadrilateralComplexSquare.comp r.continuous)
    (by intro t ht; rcases ht with rfl | rfl; exact rawQ_boundary _ k hq0; exact rawQ_boundary _ l hq1)
    (by intro t ht; rcases ht with rfl | rfl; exact rawQ_boundary _ m hr0; exact rawQ_boundary _ n hr1)
    (fun t ht0 ht1 => rawQ_open _ (hq t ht0 ht1))
    (fun t ht0 ht1 => rawQ_open _ (hr t ht0 ht1))
    (rawQ_chord_open q k l hkl hq0 hq1) (rawQ_chord_open r m n hmn hr0 hr1)
    hend hd u v hu0 hu1 hv0 hv1 hc
  exact ⟨s,t,rawQ_injective hst⟩

end Markov
