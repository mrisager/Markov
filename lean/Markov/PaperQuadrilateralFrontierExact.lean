import Markov.PaperQuadrilateralFrontierCuts

/-! The genuine topological frontier is exactly the four original closed
sides. Explicit outward perturbations prove the previously missing inclusion.
No adjacency, crossing-sign or normal-curve classification is assumed. -/

noncomputable section
open Set Topology
namespace Markov

private theorem frontierExact_not_interior_of_perturb
    (z : UpperHalfPlane) (f : ℝ → UpperHalfPlane) (hf : ContinuousAt f 0)
    (hf0 : f 0 = z) (hout : ∀ t : ℝ, 0 < t → f t ∉ paperIdealQuadrilateral) :
    z ∉ interior paperIdealQuadrilateral := by
  intro hz
  have hp : {t : ℝ | f t ∈ interior paperIdealQuadrilateral} ∈ 𝓝 0 :=
    hf (isOpen_interior.mem_nhds (hf0 ▸ hz))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hp
  have ht : r / 2 ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < r / 2)]
    linarith
  exact hout (r / 2) (by linarith) (interior_subset (hsub ht))

private def frontierExact_lower (z : UpperHalfPlane) (t : ℝ) : UpperHalfPlane :=
  ⟨⟨z.re, z.im * Real.exp (-t)⟩, mul_pos z.im_pos (Real.exp_pos (-t))⟩

private theorem frontierExact_lower_continuous (z : UpperHalfPlane) :
    Continuous (frontierExact_lower z) := by
  apply Continuous.upperHalfPlaneMk
  change Continuous (fun t : ℝ => (⟨z.re, z.im * Real.exp (-t)⟩ : ℂ))
  exact Complex.equivRealProdCLM.symm.continuous.comp
    (continuous_const.prodMk (continuous_const.mul (Real.continuous_exp.comp continuous_neg)))

private theorem frontierExact_lower_zero (z : UpperHalfPlane) : frontierExact_lower z 0 = z := by
  apply UpperHalfPlane.ext_re_im
  · rfl
  · simp [frontierExact_lower]

private theorem frontierExact_side_not_interior (k : Fin 4) (z : UpperHalfPlane)
    (hz : z ∈ paperQuadrilateralGeodesicSide k) :
    z ∉ interior paperIdealQuadrilateral := by
  fin_cases k
  · apply frontierExact_not_interior_of_perturb z (fun t : ℝ => t +ᵥ z)
      (by
        apply UpperHalfPlane.isEmbedding_coe.continuousAt_iff.mpr
        change ContinuousAt (fun t : ℝ => (t : ℂ) + (z : ℂ)) 0
        fun_prop) (zero_vadd ℝ z)
    intro t ht hmem
    have hzre : z.re = 1 := hz
    have hle := hmem.2.1
    change (t +ᵥ z).re ≤ 1 at hle
    rw [UpperHalfPlane.vadd_re, hzre] at hle
    linarith
  · apply frontierExact_not_interior_of_perturb z (fun t : ℝ => (-t) +ᵥ z)
      (by
        apply UpperHalfPlane.isEmbedding_coe.continuousAt_iff.mpr
        change ContinuousAt (fun t : ℝ => ((-t : ℝ) : ℂ) + (z : ℂ)) 0
        fun_prop) (by simp)
    intro t ht hmem
    have hzre : z.re = -1 := hz
    have hle := hmem.1
    change -1 ≤ ((-t) +ᵥ z).re at hle
    rw [UpperHalfPlane.vadd_re, hzre] at hle
    linarith
  · apply frontierExact_not_interior_of_perturb z (frontierExact_lower z)
      (frontierExact_lower_continuous z).continuousAt (frontierExact_lower_zero z)
    intro t ht hmem
    have hzside : z.re ^ 2 + z.re + z.im ^ 2 = 0 := hz
    have hlt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hpos := Real.exp_pos (-t)
    have hsq : (z.im * Real.exp (-t)) ^ 2 < z.im ^ 2 := by
      have hm : z.im * Real.exp (-t) < z.im := by
        simpa only [mul_one] using mul_lt_mul_of_pos_left hlt z.im_pos
      have hp := mul_pos z.im_pos hpos
      nlinarith
    have hle := hmem.2.2.1
    change 0 ≤ z.re ^ 2 + z.re + (z.im * Real.exp (-t)) ^ 2 at hle
    linarith
  · apply frontierExact_not_interior_of_perturb z (frontierExact_lower z)
      (frontierExact_lower_continuous z).continuousAt (frontierExact_lower_zero z)
    intro t ht hmem
    have hzside : z.re ^ 2 - z.re + z.im ^ 2 = 0 := hz
    have hlt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hpos := Real.exp_pos (-t)
    have hsq : (z.im * Real.exp (-t)) ^ 2 < z.im ^ 2 := by
      have hm : z.im * Real.exp (-t) < z.im := by
        simpa only [mul_one] using mul_lt_mul_of_pos_left hlt z.im_pos
      have hp := mul_pos z.im_pos hpos
      nlinarith
    have hle := hmem.2.2.2
    change 0 ≤ z.re ^ 2 - z.re + (z.im * Real.exp (-t)) ^ 2 at hle
    linarith

/-- Every actual original side lies on the genuine topological frontier. -/
theorem paperQuadrilateralGeodesicSide_subset_frontier (k : Fin 4) :
    paperQuadrilateralGeodesicSide k ⊆ frontier paperIdealQuadrilateral := by
  intro z hz
  exact ⟨subset_closure (paperQuadrilateralGeodesicSide_subset k hz),
    frontierExact_side_not_interior k z hz⟩

/-- The actual ideal-quadrilateral frontier is exactly the union of its four
original closed sides; ideal vertices do not belong to the upper half-plane. -/
theorem paperIdealQuadrilateral_frontier_eq_sides :
    frontier paperIdealQuadrilateral = ⋃ k : Fin 4, paperQuadrilateralGeodesicSide k := by
  apply subset_antisymm paperIdealQuadrilateral_frontier_subset_sides
  exact iUnion_subset paperQuadrilateralGeodesicSide_subset_frontier

/-- The actual topological interior is exactly the four strict original
inequalities, with no omitted boundary case. -/
theorem paperIdealQuadrilateral_interior_eq_strictRegion :
    interior paperIdealQuadrilateral = paperIdealQuadrilateralStrictRegion := by
  apply subset_antisymm _ paperIdealQuadrilateralStrictRegion_subset_interior
  intro z hz
  have hzQ := interior_subset hz
  have hside (k : Fin 4) : z ∉ paperQuadrilateralGeodesicSide k := by
    intro hk
    exact (paperQuadrilateralGeodesicSide_subset_frontier k hk).2 hz
  have h0 : z.re ≠ 1 := hside 0
  have h1 : z.re ≠ -1 := hside 1
  have h2 : z.re ^ 2 + z.re + z.im ^ 2 ≠ 0 := hside 2
  have h3 : z.re ^ 2 - z.re + z.im ^ 2 ≠ 0 := hside 3
  exact ⟨lt_of_le_of_ne hzQ.1 h1.symm, lt_of_le_of_ne hzQ.2.1 h0,
    lt_of_le_of_ne hzQ.2.2.1 h2.symm, lt_of_le_of_ne hzQ.2.2.2 h3.symm⟩

end Markov
