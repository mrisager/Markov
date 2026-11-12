import Markov.UpperHalfPlaneCayleySLBoundary

/-! Actual intersecting, noncoincident SL-translates of the vertical axis have
Cayley endpoints on opposite sides of the real diameter. No chord-crossing,
planar-separation, or simplicity premise is introduced. -/

noncomputable section
open Set
open scoped MatrixGroups
namespace Markov

private theorem axisSides_det (h : SL(2, ℝ)) :
    h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using h.det_coe

/-- Literal real-part formula along the actual positive imaginary axis. -/
theorem upperHalfPlaneSL_vertical_re (h : SL(2, ℝ)) (t : ℝ) :
    (h • hyperbolicVerticalAxis t).re =
      (h 0 0 * h 1 0 * (Real.exp t) ^ 2 + h 0 1 * h 1 1) /
        ((h 1 0) ^ 2 * (Real.exp t) ^ 2 + (h 1 1) ^ 2) := by
  change (((h • hyperbolicVerticalAxis t : UpperHalfPlane) : ℂ)).re = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  simp [Complex.div_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    hyperbolicVerticalAxis]
  ring

/-- Exact imaginary coordinate of the zero-column Cayley endpoint. -/
theorem upperHalfPlaneCayleySLZero_im (h : SL(2, ℝ)) :
    (upperHalfPlaneCayleySLZero h).im =
      (-2 * h 0 1 * h 1 1) / ((h 0 1) ^ 2 + (h 1 1) ^ 2) := by
  simp [upperHalfPlaneCayleySLZero, Complex.div_im, Complex.normSq_apply]
  ring

/-- Exact imaginary coordinate of the infinity-column Cayley endpoint. -/
theorem upperHalfPlaneCayleySLInfinity_im (h : SL(2, ℝ)) :
    (upperHalfPlaneCayleySLInfinity h).im =
      (-2 * h 0 0 * h 1 0) / ((h 0 0) ^ 2 + (h 1 0) ^ 2) := by
  simp [upperHalfPlaneCayleySLInfinity, Complex.div_im, Complex.normSq_apply]
  ring

private theorem axisSides_mem_vertical (z : UpperHalfPlane) :
    z ∈ Set.range hyperbolicVerticalAxis ↔ z.re = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    rfl
  · intro hz
    refine ⟨Real.log z.im, ?_⟩
    apply UpperHalfPlane.ext_re_im
    · exact hz.symm
    · exact Real.exp_log z.im_pos

/-- The actual zero-product cases preserve the entire vertical range.
Determinant one forces a diagonal or antidiagonal matrix, including inversion. -/
theorem upperHalfPlaneSL_vertical_range_of_products_zero
    (h : SL(2, ℝ)) (hac : h 0 0 * h 1 0 = 0) (hbd : h 0 1 * h 1 1 = 0) :
    Set.range (fun t : ℝ => h • hyperbolicVerticalAxis t) =
      Set.range hyperbolicVerticalAxis := by
  have hcases : (h 0 1 = 0 ∧ h 1 0 = 0) ∨ (h 0 0 = 0 ∧ h 1 1 = 0) := by
    rcases mul_eq_zero.mp hac with ha | hc
    · rcases mul_eq_zero.mp hbd with hb | hd
      · have he := axisSides_det h
        rw [ha, hb] at he
        norm_num at he
      · exact Or.inr ⟨ha, hd⟩
    · rcases mul_eq_zero.mp hbd with hb | hd
      · exact Or.inl ⟨hb, hc⟩
      · have he := axisSides_det h
        rw [hc, hd] at he
        norm_num at he
  have hiac : (h⁻¹) 0 0 * (h⁻¹) 1 0 = 0 := by
    rcases hcases with ⟨hb, hc⟩ | ⟨ha, hd⟩
    · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hc]
    · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hd]
  have hibd : (h⁻¹) 0 1 * (h⁻¹) 1 1 = 0 := by
    rcases hcases with ⟨hb, hc⟩ | ⟨ha, hd⟩
    · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hb]
    · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, ha]
  have hsubset (k : SL(2, ℝ)) (hka : k 0 0 * k 1 0 = 0) (hkb : k 0 1 * k 1 1 = 0) :
      Set.range (fun t : ℝ => k • hyperbolicVerticalAxis t) ⊆
        Set.range hyperbolicVerticalAxis := by
    rintro z ⟨t, rfl⟩
    apply (axisSides_mem_vertical _).mpr
    rw [upperHalfPlaneSL_vertical_re, hka, hkb]
    simp
  apply subset_antisymm (hsubset h hac hbd)
  rintro z ⟨u, rfl⟩
  obtain ⟨s, hs⟩ := hsubset h⁻¹ hiac hibd ⟨u, rfl⟩
  refine ⟨s, ?_⟩
  change h • hyperbolicVerticalAxis s = hyperbolicVerticalAxis u
  change hyperbolicVerticalAxis s = h⁻¹ • hyperbolicVerticalAxis u at hs
  rw [hs, smul_inv_smul]

private theorem axisSides_vertical_den_pos (h : SL(2, ℝ)) (y : ℝ) (hy : 0 < y) :
    0 < (h 1 0) ^ 2 * y ^ 2 + (h 1 1) ^ 2 := by
  by_contra hn
  have hc : h 1 0 = 0 := by
    have hp : (h 1 0 * y) ^ 2 = 0 := by nlinarith [sq_nonneg (h 1 1)]
    exact (mul_eq_zero.mp (sq_eq_zero_iff.mp hp)).resolve_right hy.ne'
  have hd : h 1 1 = 0 := by nlinarith [sq_nonneg (h 1 1)]
  have he := axisSides_det h
  rw [hc, hd] at he
  norm_num at he

private theorem axisSides_first_column_pos (h : SL(2, ℝ)) :
    0 < (h 0 0) ^ 2 + (h 1 0) ^ 2 := by
  have hp := Complex.normSq_pos.mpr (upperHalfPlaneCayleySLInfinity_den_ne_zero h)
  simpa [Complex.normSq_apply, pow_two] using hp

private theorem axisSides_second_column_pos (h : SL(2, ℝ)) :
    0 < (h 0 1) ^ 2 + (h 1 1) ^ 2 := by
  have hp := Complex.normSq_pos.mpr (upperHalfPlaneCayleySLZero_den_ne_zero h)
  simpa [Complex.normSq_apply, pow_two] using hp

/-- An actual crossing point of a noncoincident translated vertical axis
forces its two actual Cayley column endpoints to have opposite imaginary signs. -/
theorem upperHalfPlaneCayleySL_opposite_im_of_axis_intersection
    (h : SL(2, ℝ)) (t : ℝ) (hpoint : (h • hyperbolicVerticalAxis t).re = 0)
    (hne : Set.range (fun s : ℝ => h • hyperbolicVerticalAxis s) ≠
      Set.range hyperbolicVerticalAxis) :
    (upperHalfPlaneCayleySLZero h).im * (upperHalfPlaneCayleySLInfinity h).im < 0 := by
  rw [upperHalfPlaneSL_vertical_re] at hpoint
  have hnum : h 0 0 * h 1 0 * (Real.exp t) ^ 2 + h 0 1 * h 1 1 = 0 :=
    (div_eq_zero_iff).mp hpoint |>.resolve_right
      (axisSides_vertical_den_pos h (Real.exp t) (Real.exp_pos t)).ne'
  have hac : h 0 0 * h 1 0 ≠ 0 := by
    intro he
    have hbd : h 0 1 * h 1 1 = 0 := by rw [he, zero_mul, zero_add] at hnum; exact hnum
    exact hne (upperHalfPlaneSL_vertical_range_of_products_zero h he hbd)
  have hbd : h 0 1 * h 1 1 = -(h 0 0 * h 1 0) * (Real.exp t) ^ 2 := by linarith
  have hprod : (h 0 0 * h 1 0) * (h 0 1 * h 1 1) < 0 := by
    rw [hbd]
    have hp := mul_pos (sq_pos_of_ne_zero hac) (sq_pos_of_pos (Real.exp_pos t))
    nlinarith only [hp]
  rw [upperHalfPlaneCayleySLZero_im, upperHalfPlaneCayleySLInfinity_im,
    div_mul_div_comm]
  apply div_neg_of_neg_of_pos _
    (mul_pos (axisSides_second_column_pos h) (axisSides_first_column_pos h))
  nlinarith only [hprod]

/-- Range-intersection version retaining both actual axes and the exact
noncoincidence hypothesis. -/
theorem upperHalfPlaneCayleySL_opposite_im_of_axes_intersect
    (h : SL(2, ℝ))
    (hinter : (Set.range (fun s : ℝ => h • hyperbolicVerticalAxis s) ∩
      Set.range hyperbolicVerticalAxis).Nonempty)
    (hne : Set.range (fun s : ℝ => h • hyperbolicVerticalAxis s) ≠
      Set.range hyperbolicVerticalAxis) :
    (upperHalfPlaneCayleySLZero h).im * (upperHalfPlaneCayleySLInfinity h).im < 0 := by
  obtain ⟨z, ⟨t, ht⟩, u, hu⟩ := hinter
  apply upperHalfPlaneCayleySL_opposite_im_of_axis_intersection h t _ hne
  change h • hyperbolicVerticalAxis t = z at ht
  rw [ht, ← hu]
  rfl

/-- In particular, neither actual column endpoint lies on the real diameter. -/
theorem upperHalfPlaneCayleySL_endpoint_im_ne_zero_of_axes_intersect
    (h : SL(2, ℝ))
    (hinter : (Set.range (fun s : ℝ => h • hyperbolicVerticalAxis s) ∩
      Set.range hyperbolicVerticalAxis).Nonempty)
    (hne : Set.range (fun s : ℝ => h • hyperbolicVerticalAxis s) ≠
      Set.range hyperbolicVerticalAxis) :
    (upperHalfPlaneCayleySLZero h).im ≠ 0 ∧ (upperHalfPlaneCayleySLInfinity h).im ≠ 0 := by
  have hp := upperHalfPlaneCayleySL_opposite_im_of_axes_intersect h hinter hne
  constructor
  · intro he
    rw [he, zero_mul] at hp
    exact (lt_irrefl 0 hp)
  · intro he
    rw [he, mul_zero] at hp
    exact (lt_irrefl 0 hp)

end Markov
