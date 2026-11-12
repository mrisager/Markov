import Markov.ConvexDiskRadialObstruction

/-! An actual based radial frontier loop and its finite extension obstruction.
The two actual normalized based path homotopies are constructed from the stated
continuous maps and pointwise laws. No separation or winding field is assumed. -/

noncomputable section
open Set Topology Metric
namespace Markov

/-- The actual continuous normalization map from nonzero complex numbers to Circle. -/
def complexUnitDirection : C({z : ℂ // z ≠ 0}, Circle) where
  toFun z := ⟨NormedSpace.normalize z.val,
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize z.property)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun z : {z : ℂ // z ≠ 0} => ‖z.val‖⁻¹ • z.val)
    exact (continuous_subtype_val.norm.inv₀ (fun z => norm_ne_zero_iff.mpr z.property)).smul
      continuous_subtype_val

private def circleHomeo : NormalizedCircle ≃ₜ Circle :=
  AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)

private theorem circleHomeo_zero : circleHomeo (0 : NormalizedCircle) = 1 := by
  simp [circleHomeo, AddCircle.homeomorphCircle_apply]

private def basedDirection (a : Circle) : C({z : ℂ // z ≠ 0}, NormalizedCircle) where
  toFun z := circleHomeo.symm (complexUnitDirection z / a)
  continuous_toFun := by
    simp_rw [div_eq_mul_inv]
    fun_prop

private theorem frontier_ne_zero (P : Set ℂ) (hc : Convex ℝ P) (h0 : P ∈ 𝓝 0)
    (z : ↥(frontier P)) : z.val ≠ 0 := by
  intro hz
  have hg := (gauge_eq_one_iff_mem_frontier hc h0).mpr z.property
  rw [hz, gauge_zero] at hg
  exact zero_ne_one hg

/-- The actual radial frontier loop through a prescribed boundary point. The
circle parameter is rotated by the actual inverse radial image of that point. -/
def convexFrontierBasedLoop (P : Set ℂ) (hc : Convex ℝ P)
    (h0 : P ∈ 𝓝 0) (hb : Bornology.IsBounded P) (w0 : ↥(frontier P)) : Path w0 w0 where
  toFun t := convexDiskRadialBoundaryHomeomorph P hc h0 hb
    ((convexDiskRadialBoundaryHomeomorph P hc h0 hb).symm w0 *
      circleHomeo (normalizedCircleStandardLoop t))
  continuous_toFun := by fun_prop
  source' := by rw [normalizedCircleStandardLoop.source, circleHomeo_zero, mul_one]; exact
    (convexDiskRadialBoundaryHomeomorph P hc h0 hb).apply_symm_apply w0
  target' := by rw [normalizedCircleStandardLoop.target, circleHomeo_zero, mul_one]; exact
    (convexDiskRadialBoundaryHomeomorph P hc h0 hb).apply_symm_apply w0

/-- The normalized actual frontier loop is literally the chosen circle rotation
of the actual positive once-around loop. -/
theorem convexFrontierBasedLoop_normalize (P : Set ℂ) (hc : Convex ℝ P)
    (h0 : P ∈ 𝓝 0) (hb : Bornology.IsBounded P) (w0 : ↥(frontier P)) (t : unitInterval) :
    NormedSpace.normalize (convexFrontierBasedLoop P hc h0 hb w0 t).val =
      (((convexDiskRadialBoundaryHomeomorph P hc h0 hb).symm w0 *
        (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0))
          (normalizedCircleStandardLoop t) : Circle) : ℂ) := by
  exact convexDiskRadialHomeomorph_normalize_circle P hc h0 hb _

private theorem basedDirection_frontier_loop (P : Set ℂ) (hc : Convex ℝ P)
    (h0 : P ∈ 𝓝 0) (hb : Bornology.IsBounded P) (w0 : ↥(frontier P)) (t : unitInterval) :
    basedDirection ((convexDiskRadialBoundaryHomeomorph P hc h0 hb).symm w0)
      ⟨(convexFrontierBasedLoop P hc h0 hb w0 t).val, frontier_ne_zero P hc h0 _⟩ =
        normalizedCircleStandardLoop t := by
  change circleHomeo.symm (_ / _) = _
  have hn : complexUnitDirection
      ⟨(convexFrontierBasedLoop P hc h0 hb w0 t).val, frontier_ne_zero P hc h0 _⟩ =
      (convexDiskRadialBoundaryHomeomorph P hc h0 hb).symm w0 *
        circleHomeo (normalizedCircleStandardLoop t) := by
    apply Circle.ext
    exact convexFrontierBasedLoop_normalize P hc h0 hb w0 t
  rw [hn, mul_div_cancel_left, circleHomeo.symm_apply_apply]

private def frontierLoopContraction (P : Set ℂ) (hc : Convex ℝ P)
    (w0 : ↥(frontier P)) (β : Path w0 w0) (s t : unitInterval) : ↥(closure P) :=
  ⟨(1 - (s : ℝ)) • (β t).val + (s : ℝ) • w0.val,
    hc.closure (frontier_subset_closure (β t).property) (frontier_subset_closure w0.property)
      (sub_nonneg.mpr s.property.2) s.property.1 (by ring)⟩

private theorem frontierLoopContraction_continuous (P : Set ℂ) (hc : Convex ℝ P)
    (w0 : ↥(frontier P)) (β : Path w0 w0) :
    Continuous (fun st : unitInterval × unitInterval => frontierLoopContraction P hc w0 β st.1 st.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun st : unitInterval × unitInterval =>
    (1 - (st.1 : ℝ)) • (β st.2).val + (st.1 : ℝ) • w0.val)
  fun_prop

private theorem frontierLoopContraction_zero (P : Set ℂ) (hc : Convex ℝ P)
    (w0 : ↥(frontier P)) (β : Path w0 w0) (t : unitInterval) :
    frontierLoopContraction P hc w0 β 0 t = ⟨(β t).val, frontier_subset_closure (β t).property⟩ := by
  apply Subtype.ext
  simp [frontierLoopContraction]

private theorem frontierLoopContraction_one (P : Set ℂ) (hc : Convex ℝ P)
    (w0 : ↥(frontier P)) (β : Path w0 w0) (t : unitInterval) :
    frontierLoopContraction P hc w0 β 1 t = ⟨w0.val, frontier_subset_closure w0.property⟩ := by
  apply Subtype.ext
  simp [frontierLoopContraction]

private theorem frontierLoopContraction_base (P : Set ℂ) (hc : Convex ℝ P)
    (w0 : ↥(frontier P)) (β : Path w0 w0) (s t : unitInterval) (ht : t = 0 ∨ t = 1) :
    frontierLoopContraction P hc w0 β s t = ⟨w0.val, frontier_subset_closure w0.property⟩ := by
  have he : β t = w0 := by rcases ht with rfl | rfl; exact β.source; exact β.target
  apply Subtype.ext
  simp only [frontierLoopContraction, he, sub_smul, one_smul]
  module

/-- A continuous map on the actual convex disk has a zero if its boundary is
actually homotoped to the literal frontier inclusion through nonzero values,
fixing one actual boundary point. The proof constructs a radial based loop,
a normalized homotopy to standardLoop, and a normalized based null-homotopy. -/
theorem convexFrontier_boundary_homotopy_has_zero
    (P : Set ℂ) (hc : Convex ℝ P) (h0 : P ∈ 𝓝 0) (hb : Bornology.IsBounded P)
    (w0 : ↥(frontier P)) (F : ↥(closure P) → ℂ) (hF : Continuous F)
    (H : unitInterval × ↥(frontier P) → ℂ) (hH : Continuous H)
    (hH0 : ∀ z : ↥(frontier P), H (0, z) = F ⟨z.val, frontier_subset_closure z.property⟩)
    (hH1 : ∀ z : ↥(frontier P), H (1, z) = z.val)
    (hHb : ∀ s : unitInterval, H (s, w0) = w0.val)
    (hHn : ∀ st : unitInterval × ↥(frontier P), H st ≠ 0) :
    ∃ z : ↥(closure P), F z = 0 := by
  classical
  by_contra hn
  have hFn : ∀ z : ↥(closure P), F z ≠ 0 := by simpa only [not_exists] using hn
  let β := convexFrontierBasedLoop P hc h0 hb w0
  let a := (convexDiskRadialBoundaryHomeomorph P hc h0 hb).symm w0
  let N := basedDirection a
  have hNb : N ⟨w0.val, frontier_ne_zero P hc h0 w0⟩ = 0 := by
    have he := basedDirection_frontier_loop P hc h0 hb w0 0
    rw [(convexFrontierBasedLoop P hc h0 hb w0).source, normalizedCircleStandardLoop.source] at he
    exact he
  have hFw0 : F ⟨w0.val, frontier_subset_closure w0.property⟩ = w0.val :=
    (hH0 w0).symm.trans (hHb 0)
  let α : Path (0 : NormalizedCircle) 0 :=
    { toFun := fun t => N ⟨H (0, β t), hHn (0, β t)⟩
      continuous_toFun := N.continuous.comp
        ((hH.comp (continuous_const.prodMk β.continuous)).subtype_mk _)
      source' := by
        apply Eq.trans _ hNb
        apply congrArg N
        exact Subtype.ext (show H (0, β 0) = w0.val by rw [β.source, hHb])
      target' := by
        apply Eq.trans _ hNb
        apply congrArg N
        exact Subtype.ext (show H (0, β 1) = w0.val by rw [β.target, hHb]) }
  have hs : α.Homotopic normalizedCircleStandardLoop := by
    refine ⟨{ toFun := fun st => N ⟨H (st.1, β st.2), hHn (st.1, β st.2)⟩
              continuous_toFun := N.continuous.comp
                ((hH.comp (continuous_fst.prodMk (β.continuous.comp continuous_snd))).subtype_mk _)
              map_zero_left := fun _ => rfl
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro t
      change N ⟨H (1, β t), _⟩ = normalizedCircleStandardLoop t
      calc
        N ⟨H (1, β t), _⟩ = N ⟨(β t).val, frontier_ne_zero P hc h0 _⟩ :=
          congrArg N (Subtype.ext (hH1 (β t)))
        _ = normalizedCircleStandardLoop t := basedDirection_frontier_loop P hc h0 hb w0 t
    · intro s t ht
      have he : β t = w0 := by rcases ht with rfl | rfl; exact β.source; exact β.target
      change N ⟨H (s, β t), _⟩ = N ⟨H (0, β t), _⟩
      apply congrArg N
      exact Subtype.ext (by simp only [he, hHb])
  have hcα : α.Homotopic (Path.refl (0 : NormalizedCircle)) := by
    refine ⟨{ toFun := fun st => N ⟨F (frontierLoopContraction P hc w0 β st.1 st.2), hFn _⟩
              continuous_toFun := N.continuous.comp
                ((hF.comp (frontierLoopContraction_continuous P hc w0 β)).subtype_mk _)
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro t
      change N ⟨F (frontierLoopContraction P hc w0 β 0 t), _⟩ = N ⟨H (0, β t), _⟩
      apply congrArg N
      exact Subtype.ext (show F (frontierLoopContraction P hc w0 β 0 t) = H (0, β t) by
        rw [frontierLoopContraction_zero, hH0])
    · intro t
      change N ⟨F (frontierLoopContraction P hc w0 β 1 t), _⟩ = 0
      apply Eq.trans _ hNb
      apply congrArg N
      exact Subtype.ext (show F (frontierLoopContraction P hc w0 β 1 t) = w0.val by
        rw [frontierLoopContraction_one, hFw0])
    · intro s t ht
      have he : β t = w0 := by rcases ht with rfl | rfl; exact β.source; exact β.target
      change N ⟨F (frontierLoopContraction P hc w0 β s t), _⟩ = N ⟨H (0, β t), _⟩
      apply congrArg N
      exact Subtype.ext (show F (frontierLoopContraction P hc w0 β s t) = H (0, β t) by
        rw [frontierLoopContraction_base P hc w0 β s t ht, hFw0, he, hHb])
  exact normalizedCircleStandardLoop_not_homotopic_refl (hs.symm.trans hcα)

end Markov
