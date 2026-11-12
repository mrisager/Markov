import Markov.ConvexFrontierLoopObstruction
import Markov.DiskArcChordHomotopy
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Finite crossing from actual transverse interior chord intersection.
All topology is supplied by the checked actual based frontier-loop obstruction;
the rectangle and chord-linear inverse are explicitly constructed. -/

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

/-- Actual continuous disk arcs intersect when their actual endpoint chords
have a transverse intersection at strictly interior parameters. Every square,
linear inverse, boundary homotopy and based loop is constructed in the proof. -/
theorem diskArcs_intersect_of_transverse_interior_chords
    (f g : unitInterval → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ‖f 0‖ = 1) (hf1 : ‖f 1‖ = 1) (hfn : f 0 ≠ f 1)
    (hg0 : ‖g 0‖ = 1) (hg1 : ‖g 1‖ = 1) (hgn : g 0 ≠ g 1)
    (hfi : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → ‖f t‖ < 1)
    (hgi : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → ‖g t‖ < 1)
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
    have hne := diskArcChordHomotopy_boundary_ne f g hf0 hf1 hfn hg0 hg1 hgn hfi hgi hend
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

end Markov
