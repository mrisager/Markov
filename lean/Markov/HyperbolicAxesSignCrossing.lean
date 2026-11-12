import Markov.HyperbolicAxesSingleIntersection

/-! Genuine sign-changing crossings of actual hyperbolic lines. The sign is
measured by the real coordinate in an actual SL chart of the crossed line.
Noncoincidence and the actual intersection replace any transversality premise.
No polygon transition, finite matching or normal form is assumed. -/

noncomputable section
open Set
open scoped MatrixGroups
namespace Markov

private theorem signCrossing_den_pos (h : SL(2, ℝ)) (t : ℝ) :
    0 < (h 1 0) ^ 2 * (Real.exp t) ^ 2 + (h 1 1) ^ 2 := by
  by_contra hn
  have hc : h 1 0 = 0 := by
    have hp : (h 1 0 * Real.exp t) ^ 2 = 0 := by
      nlinarith [sq_nonneg (h 1 1)]
    exact (mul_eq_zero.mp (sq_eq_zero_iff.mp hp)).resolve_right (Real.exp_pos t).ne'
  have hd : h 1 1 = 0 := by nlinarith [sq_nonneg (h 1 1)]
  have he : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using h.det_coe
  rw [hc, hd] at he
  norm_num at he

/-- An actual noncoincident translated vertical line genuinely changes side
at its actual intersection with the vertical line. This holds for every pair
of source parameters strictly on opposite sides of the intersection parameter. -/
theorem upperHalfPlaneSL_vertical_crossing_sign_mul_neg
    (h : SL(2, ℝ))
    (hne : Set.range (fun t : ℝ => h • hyperbolicVerticalAxis t) ≠
      Set.range hyperbolicVerticalAxis)
    (t₀ : ℝ) (hroot : (h • hyperbolicVerticalAxis t₀).re = 0)
    (s u : ℝ) (hs : s < t₀) (hu : t₀ < u) :
    (h • hyperbolicVerticalAxis s).re * (h • hyperbolicVerticalAxis u).re < 0 := by
  have hnum : h 0 0 * h 1 0 * (Real.exp t₀) ^ 2 + h 0 1 * h 1 1 = 0 := by
    rw [upperHalfPlaneSL_vertical_re] at hroot
    exact ((div_eq_zero_iff).mp hroot).resolve_right (signCrossing_den_pos h t₀).ne'
  have hac : h 0 0 * h 1 0 ≠ 0 := by
    intro he
    have hbd : h 0 1 * h 1 1 = 0 := by
      rw [he, zero_mul, zero_add] at hnum
      exact hnum
    exact hne (upperHalfPlaneSL_vertical_range_of_products_zero h he hbd)
  have hbd : h 0 1 * h 1 1 = -(h 0 0 * h 1 0) * (Real.exp t₀) ^ 2 := by
    linarith only [hnum]
  have hs2 : (Real.exp s) ^ 2 < (Real.exp t₀) ^ 2 :=
    (sq_lt_sq₀ (Real.exp_pos s).le (Real.exp_pos t₀).le).mpr (Real.exp_lt_exp.mpr hs)
  have hu2 : (Real.exp t₀) ^ 2 < (Real.exp u) ^ 2 :=
    (sq_lt_sq₀ (Real.exp_pos t₀).le (Real.exp_pos u).le).mpr (Real.exp_lt_exp.mpr hu)
  rw [upperHalfPlaneSL_vertical_re, upperHalfPlaneSL_vertical_re, div_mul_div_comm]
  apply div_neg_of_neg_of_pos _ (mul_pos (signCrossing_den_pos h s) (signCrossing_den_pos h u))
  rw [hbd]
  convert mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hac)
    (mul_neg_of_neg_of_pos (sub_neg.mpr hs2) (sub_pos.mpr hu2)) using 1
  ring

private theorem signCrossing_phase_range
    (β : ℝ → UpperHalfPlane) (B : SL(2, ℝ)) (d : ℝ)
    (hβ : ∀ t, β t = B • hyperbolicVerticalAxis (t + d)) :
    Set.range β = Set.range (fun t : ℝ => B • hyperbolicVerticalAxis t) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t + d, (hβ t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t - d, ?_⟩
    simpa only [sub_add_cancel] using hβ (t - d)

private theorem signCrossing_image_range (A B : SL(2, ℝ)) :
    (fun z : UpperHalfPlane => A⁻¹ • z) ''
        Set.range (fun t : ℝ => B • hyperbolicVerticalAxis t) =
      Set.range (fun t : ℝ => (A⁻¹ * B) • hyperbolicVerticalAxis t) := by
  rw [← Set.range_comp']
  simp only [mul_smul]

/-- Any actual isometric line meeting a noncoincident actual SL axis changes
side in that exact axis chart. The actual chart and source orientation remain
fixed in the conclusion. -/
theorem upperHalfPlane_isometric_line_crosses_SL_axis
    (A : SL(2, ℝ)) (β : ℝ → UpperHalfPlane) (hβ : Isometry β)
    (hne : Set.range β ≠ Set.range (fun t : ℝ => A • hyperbolicVerticalAxis t))
    (t₀ : ℝ) (hroot : (A⁻¹ • β t₀).re = 0)
    (s u : ℝ) (hs : s < t₀) (hu : t₀ < u) :
    (A⁻¹ • β s).re * (A⁻¹ • β u).re < 0 := by
  obtain ⟨B, d, hd⟩ := upperHalfPlane_locally_unit_speed_eq_conjugate_vertical β
    (fun _ => ⟨1, by norm_num, fun s _ t _ => hβ.dist_eq s t⟩)
  have hrange := signCrossing_phase_range β B d hd
  have hnorm : Set.range (fun t : ℝ => (A⁻¹ * B) • hyperbolicVerticalAxis t) ≠
      Set.range hyperbolicVerticalAxis := by
    intro he
    apply hne
    rw [hrange]
    apply (Set.image_eq_image (f := fun z : UpperHalfPlane => A⁻¹ • z)
      (s := Set.range (fun t : ℝ => B • hyperbolicVerticalAxis t))
      (t := Set.range (fun t : ℝ => A • hyperbolicVerticalAxis t))
      (isometry_smul UpperHalfPlane A⁻¹).injective).mp
    rw [signCrossing_image_range, signCrossing_image_range]
    simpa only [inv_mul_cancel, one_smul] using he
  have hroot' : ((A⁻¹ * B) • hyperbolicVerticalAxis (t₀ + d)).re = 0 := by
    simpa only [hd, mul_smul] using hroot
  have hcross := upperHalfPlaneSL_vertical_crossing_sign_mul_neg (A⁻¹ * B) hnorm
    (t₀ + d) hroot' (s + d) (u + d) (by linarith) (by linarith)
  simpa only [hd, mul_smul] using hcross

/-- Arbitrary actual distinct isometric real lines genuinely cross at an
actual common point. The theorem constructs an actual SL chart of the first
line, retains its phase, and proves opposite real-coordinate signs for every
pair of second-line source parameters around the given intersection. -/
theorem upperHalfPlane_distinct_isometric_lines_cross_in_axis_chart
    (α β : ℝ → UpperHalfPlane) (hα : Isometry α) (hβ : Isometry β)
    (hne : Set.range β ≠ Set.range α) (v₀ t₀ : ℝ) (hpoint : β t₀ = α v₀) :
    ∃ A : SL(2, ℝ), ∃ c : ℝ,
      (∀ t : ℝ, α t = A • hyperbolicVerticalAxis (t + c)) ∧
      ∀ s u : ℝ, s < t₀ → t₀ < u →
        (A⁻¹ • β s).re * (A⁻¹ • β u).re < 0 := by
  obtain ⟨A, c, hc⟩ := upperHalfPlane_locally_unit_speed_eq_conjugate_vertical α
    (fun _ => ⟨1, by norm_num, fun s _ t _ => hα.dist_eq s t⟩)
  have hrange := signCrossing_phase_range α A c hc
  have hroot : (A⁻¹ • β t₀).re = 0 := by
    rw [hpoint, hc v₀, inv_smul_smul]
    rfl
  refine ⟨A, c, hc, ?_⟩
  intro s u hs hu
  exact upperHalfPlane_isometric_line_crosses_SL_axis A β hβ (by simpa only [← hrange] using hne)
    t₀ hroot s u hs hu

end Markov
