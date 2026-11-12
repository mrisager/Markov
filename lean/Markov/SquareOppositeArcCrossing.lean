import Markov.ConvexFrontierLoopObstruction
import Markov.DiskArcChordHomotopy
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Concrete square crossing from actual opposite-edge endpoints. All actual
chord parameters and the boundary obstruction are constructed. -/

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

private theorem rectangle_scalar_combo (a b r : ℝ)
    (ha : -1<a ∧ a<1) (hb : -1<b ∧ b<1) (hr0 : 0≤r) (hr1 : r≤1) :
    -1 < (1-r)*a+r*b ∧ (1-r)*a+r*b < 1 := by
  simpa only [smul_eq_mul] using
    (convex_Ioo (-1:ℝ) 1) ha hb (sub_nonneg.mpr hr1) hr0 (by ring)

private theorem rectangleArcHomotopy_boundary_ne
    (f g : unitInterval → ℂ)
    (hf0 : (f 0).im=1) (hf1 : (f 1).im= -1)
    (hg0 : (g 0).re=1) (hg1 : (g 1).re= -1)
    (hfre : ∀ t, -1<(f t).re ∧ (f t).re<1)
    (hgim : ∀ t, -1<(g t).im ∧ (g t).im<1)
    (s t u : unitInterval) (hb : (t=0 ∨ t=1) ∨ (u=0 ∨ u=1)) :
    diskArcChordHomotopy f s t ≠ diskArcChordHomotopy g s u := by
  have hfch : -1<(diskArcChord f t).re ∧ (diskArcChord f t).re<1 := by
    simpa [diskArcChord] using rectangle_scalar_combo (f 0).re (f 1).re (t:ℝ)
      (hfre 0) (hfre 1) t.property.1 t.property.2
  have hgh : -1<(diskArcChord g u).im ∧ (diskArcChord g u).im<1 := by
    simpa [diskArcChord] using rectangle_scalar_combo (g 0).im (g 1).im (u:ℝ)
      (hgim 0) (hgim 1) u.property.1 u.property.2
  have hfh : -1<(diskArcChordHomotopy f s t).re ∧ (diskArcChordHomotopy f s t).re<1 := by
    simpa [diskArcChordHomotopy] using rectangle_scalar_combo (f t).re (diskArcChord f t).re
      (s:ℝ) (hfre t) hfch s.property.1 s.property.2
  have hgh' : -1<(diskArcChordHomotopy g s u).im ∧ (diskArcChordHomotopy g s u).im<1 := by
    simpa [diskArcChordHomotopy] using rectangle_scalar_combo (g u).im (diskArcChord g u).im
      (s:ℝ) (hgim u) hgh s.property.1 s.property.2
  intro heq
  rcases hb with ht | hu
  · rw [diskArcChordHomotopy_fixed_endpoints f s t ht] at heq
    have hi := congrArg Complex.im heq
    rcases ht with rfl | rfl <;> simp only [hf0, hf1] at hi <;> linarith [hgh'.1,hgh'.2]
  · rw [diskArcChordHomotopy_fixed_endpoints g s u hu] at heq
    have hr := congrArg Complex.re heq
    rcases hu with rfl | rfl <;> simp only [hg0,hg1] at hr <;> linarith [hfh.1,hfh.2]

/-- The actual boundary obstruction for opposite-edge coordinate arcs,
with the chord data supplied internally by the public construction below. -/
private theorem rectangleArcs_intersect_of_transverse_interior_chords
    (f g : unitInterval → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : (f 0).im=1) (hf1 : (f 1).im= -1)
    (hg0 : (g 0).re=1) (hg1 : (g 1).re= -1)
    (hfre : ∀ t, -1<(f t).re ∧ (f t).re<1)
    (hgim : ∀ t, -1<(g t).im ∧ (g t).im<1)
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
    have hne := rectangleArcHomotopy_boundary_ne f g hf0 hf1 hg0 hg1 hfre hgim
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

/-- Actual opposite-edge endpoints give explicit transverse endpoint-chord
intersection at strictly interior parameters. No crossing witness is supplied. -/
theorem squareOppositeChords_data
    (f g : unitInterval → ℂ)
    (hf0 : (f 0).im=1) (hf1 : (f 1).im= -1)
    (hg0 : (g 0).re=1) (hg1 : (g 1).re= -1)
    (hx0 : -1<(f 0).re ∧ (f 0).re<1) (hx1 : -1<(f 1).re ∧ (f 1).re<1)
    (hy0 : -1<(g 0).im ∧ (g 0).im<1) (hy1 : -1<(g 1).im ∧ (g 1).im<1) :
    ∃ u v : unitInterval, 0<(u:ℝ) ∧ (u:ℝ)<1 ∧ 0<(v:ℝ) ∧ (v:ℝ)<1 ∧
      (f 1-f 0).re*(g 1-g 0).im-(f 1-f 0).im*(g 1-g 0).re ≠ 0 ∧
      diskArcChord f u = diskArcChord g v := by
  let x0 := (f 0).re
  let x1 := (f 1).re
  let y0 := (g 0).im
  let y1 := (g 1).im
  let D := 4-(x1-x0)*(y1-y0)
  let U := (1+x0)*(1-y0)+(1-x0)*(1-y1)
  let V := (1+y0)*(1-x0)+(1-y0)*(1-x1)
  have hU : 0<U := add_pos
    (mul_pos (by linarith [hx0.1]) (by linarith [hy0.2]))
    (mul_pos (by linarith [hx0.2]) (by linarith [hy1.2]))
  have hV : 0<V := add_pos
    (mul_pos (by linarith [hy0.1]) (by linarith [hx0.2]))
    (mul_pos (by linarith [hy0.2]) (by linarith [hx1.2]))
  have hDU : 0<D-U := by
    have hp := add_pos
      (mul_pos (by linarith [hx1.1] : 0<1+x1) (by linarith [hy0.1] : 0<1+y0))
      (mul_pos (by linarith [hx1.2] : 0<1-x1) (by linarith [hy1.1] : 0<1+y1))
    dsimp only [D,U]
    nlinarith
  have hDV : 0<D-V := by
    have hp := add_pos
      (mul_pos (by linarith [hy1.1] : 0<1+y1) (by linarith [hx0.1] : 0<1+x0))
      (mul_pos (by linarith [hy1.2] : 0<1-y1) (by linarith [hx1.1] : 0<1+x1))
    dsimp only [D,V]
    nlinarith
  have hD : 0<D := by linarith
  let u : unitInterval := ⟨U/D, ⟨(div_pos hU hD).le, (div_le_iff₀ hD).mpr (by linarith)⟩⟩
  let v : unitInterval := ⟨V/D, ⟨(div_pos hV hD).le, (div_le_iff₀ hD).mpr (by linarith)⟩⟩
  refine ⟨u,v,div_pos hU hD,(div_lt_iff₀ hD).mpr (by linarith),
    div_pos hV hD,(div_lt_iff₀ hD).mpr (by linarith),?_,?_⟩
  · simp only [Complex.sub_re,Complex.sub_im,hf0,hf1,hg0,hg1]
    intro heq
    dsimp only [D,x0,x1,y0,y1] at hD
    nlinarith
  · apply Complex.ext <;>
      simp [diskArcChord,u,v,hf0,hf1,hg0,hg1] <;>
      field_simp [ne_of_gt hD] <;>
      dsimp only [D,U,V,x0,x1,y0,y1] <;> ring

/-- Actual continuous top-to-bottom and right-to-left square arcs must
intersect. The transverse interior chord data is constructed, and the actual
convex-frontier loop obstruction proves crossing. Only literal coordinate
bounds and endpoint equations are supplied. -/
theorem squareArcs_top_bottom_right_left_intersect
    (f g : unitInterval → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : (f 0).im=1) (hf1 : (f 1).im= -1)
    (hg0 : (g 0).re=1) (hg1 : (g 1).re= -1)
    (hfre : ∀ t, -1<(f t).re ∧ (f t).re<1)
    (hgim : ∀ t, -1<(g t).im ∧ (g t).im<1) :
    ∃ s t : unitInterval, f s=g t := by
  obtain ⟨u,v,hu0,hu1,hv0,hv1,hd,hr⟩ := squareOppositeChords_data f g hf0 hf1 hg0 hg1
    (hfre 0) (hfre 1) (hgim 0) (hgim 1)
  exact rectangleArcs_intersect_of_transverse_interior_chords f g hf hg hf0 hf1 hg0 hg1
    hfre hgim hd u v hu0 hu1 hv0 hv1 hr

end Markov
