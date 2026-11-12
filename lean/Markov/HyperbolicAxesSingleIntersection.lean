import Markov.UpperHalfPlaneCayleyAxisSides
import Markov.HyperbolicLocalStraightening

/-! Actual distinct hyperbolic lines have at most one intersection. Coincident
ranges are explicitly excluded. No local-finiteness, non-tangency or simple-curve
classification assertion is contained in this module. -/

noncomputable section
open Set
open scoped MatrixGroups
namespace Markov

private theorem singleIntersection_den_pos (h : SL(2, ℝ)) (t : ℝ) :
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

private theorem singleIntersection_num_zero (h : SL(2, ℝ)) (t : ℝ)
    (ht : (h • hyperbolicVerticalAxis t).re = 0) :
    h 0 0 * h 1 0 * (Real.exp t) ^ 2 + h 0 1 * h 1 1 = 0 := by
  rw [upperHalfPlaneSL_vertical_re] at ht
  exact ((div_eq_zero_iff).mp ht).resolve_right (singleIntersection_den_pos h t).ne'

/-- A noncoincident translated vertical line has at most one parameter whose
actual image lies on the vertical line. -/
theorem upperHalfPlaneSL_vertical_intersection_parameter_unique
    (h : SL(2, ℝ))
    (hne : Set.range (fun s : ℝ => h • hyperbolicVerticalAxis s) ≠
      Set.range hyperbolicVerticalAxis)
    (t u : ℝ) (ht : (h • hyperbolicVerticalAxis t).re = 0)
    (hu : (h • hyperbolicVerticalAxis u).re = 0) : t = u := by
  have htn := singleIntersection_num_zero h t ht
  have hun := singleIntersection_num_zero h u hu
  have hac : h 0 0 * h 1 0 ≠ 0 := by
    intro he
    have hbd : h 0 1 * h 1 1 = 0 := by
      rw [he, zero_mul, zero_add] at htn
      exact htn
    exact hne (upperHalfPlaneSL_vertical_range_of_products_zero h he hbd)
  have he : (h 0 0 * h 1 0) * ((Real.exp t) ^ 2 - (Real.exp u) ^ 2) = 0 := by
    linear_combination htn - hun
  have hs : (Real.exp t) ^ 2 = (Real.exp u) ^ 2 :=
    sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hac)
  have hexp : Real.exp t = Real.exp u := by
    nlinarith [Real.exp_pos t, Real.exp_pos u]
  exact Real.exp_injective hexp

/-- Two distinct actual intersection parameters force equality of the whole
translated and vertical ranges; the coincidence alternative is retained. -/
theorem upperHalfPlaneSL_vertical_range_eq_of_two_intersections
    (h : SL(2, ℝ)) (t u : ℝ) (htu : t ≠ u)
    (ht : (h • hyperbolicVerticalAxis t).re = 0)
    (hu : (h • hyperbolicVerticalAxis u).re = 0) :
    Set.range (fun s : ℝ => h • hyperbolicVerticalAxis s) =
      Set.range hyperbolicVerticalAxis := by
  by_contra hne
  exact htu (upperHalfPlaneSL_vertical_intersection_parameter_unique h hne t u ht hu)

private theorem singleIntersection_inverse_image_range (A B : SL(2, ℝ)) :
    (fun z : UpperHalfPlane => A⁻¹ • z) ''
        Set.range (fun t : ℝ => B • hyperbolicVerticalAxis t) =
      Set.range (fun t : ℝ => (A⁻¹ * B) • hyperbolicVerticalAxis t) := by
  rw [← Set.range_comp']
  simp only [mul_smul]

/-- Any two actual SL-translates of the vertical line have at most one
common point unless their entire ranges coincide. -/
theorem upperHalfPlaneSL_distinct_axes_intersection_subsingleton
    (A B : SL(2, ℝ))
    (hne : Set.range (fun t : ℝ => B • hyperbolicVerticalAxis t) ≠
      Set.range (fun t : ℝ => A • hyperbolicVerticalAxis t)) :
    (Set.range (fun t : ℝ => B • hyperbolicVerticalAxis t) ∩
      Set.range (fun t : ℝ => A • hyperbolicVerticalAxis t)).Subsingleton := by
  have hnorm : Set.range (fun t : ℝ => (A⁻¹ * B) • hyperbolicVerticalAxis t) ≠
      Set.range hyperbolicVerticalAxis := by
    intro he
    apply hne
    apply (Set.image_eq_image (f := fun z : UpperHalfPlane => A⁻¹ • z)
      (s := Set.range (fun t : ℝ => B • hyperbolicVerticalAxis t))
      (t := Set.range (fun t : ℝ => A • hyperbolicVerticalAxis t))
      (isometry_smul UpperHalfPlane A⁻¹).injective).mp
    rw [singleIntersection_inverse_image_range, singleIntersection_inverse_image_range]
    simpa only [inv_mul_cancel, one_smul] using he
  rintro z ⟨⟨t, ht⟩, s, hs⟩ w ⟨⟨u, hu⟩, v, hv⟩
  have htr : ((A⁻¹ * B) • hyperbolicVerticalAxis t).re = 0 := by
    have hh := congrArg (fun x : UpperHalfPlane => A⁻¹ • x) (ht.trans hs.symm)
    simpa only [mul_smul, inv_smul_smul] using congrArg UpperHalfPlane.re hh
  have hur : ((A⁻¹ * B) • hyperbolicVerticalAxis u).re = 0 := by
    have hh := congrArg (fun x : UpperHalfPlane => A⁻¹ • x) (hu.trans hv.symm)
    simpa only [mul_smul, inv_smul_smul] using congrArg UpperHalfPlane.re hh
  have htu := upperHalfPlaneSL_vertical_intersection_parameter_unique (A⁻¹ * B)
    hnorm t u htr hur
  exact ht.symm.trans ((congrArg (fun x : ℝ => B • hyperbolicVerticalAxis x) htu).trans hu)

private theorem singleIntersection_chart_range
    (γ : ℝ → UpperHalfPlane) (A : SL(2, ℝ)) (c : ℝ)
    (hγ : ∀ t, γ t = A • hyperbolicVerticalAxis (t + c)) :
    Set.range γ = Set.range (fun t : ℝ => A • hyperbolicVerticalAxis t) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t + c, (hγ t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t - c, ?_⟩
    simpa only [sub_add_cancel] using hγ (t - c)

/-- Two arbitrary actual isometric real lines in the upper half-plane have
at most one common point, with distinct actual ranges explicitly assumed. -/
theorem upperHalfPlane_distinct_isometric_lines_intersection_subsingleton
    (α β : ℝ → UpperHalfPlane) (hα : Isometry α) (hβ : Isometry β)
    (hne : Set.range β ≠ Set.range α) :
    (Set.range β ∩ Set.range α).Subsingleton := by
  obtain ⟨A, c, hc⟩ := upperHalfPlane_locally_unit_speed_eq_conjugate_vertical α
    (fun _ => ⟨1, by norm_num, fun s _ t _ => hα.dist_eq s t⟩)
  obtain ⟨B, d, hd⟩ := upperHalfPlane_locally_unit_speed_eq_conjugate_vertical β
    (fun _ => ⟨1, by norm_num, fun s _ t _ => hβ.dist_eq s t⟩)
  have hra := singleIntersection_chart_range α A c hc
  have hrb := singleIntersection_chart_range β B d hd
  rw [hra, hrb] at hne ⊢
  exact upperHalfPlaneSL_distinct_axes_intersection_subsingleton A B hne

/-- The same actual line intersection statement retains both unique source
parameters, so a fixed noncoincident edge cannot be met twice. -/
theorem upperHalfPlane_distinct_isometric_lines_intersection_parameters_unique
    (α β : ℝ → UpperHalfPlane) (hα : Isometry α) (hβ : Isometry β)
    (hne : Set.range β ≠ Set.range α)
    (s t u v : ℝ) (hst : α s = β t) (huv : α u = β v) : s = u ∧ t = v := by
  have hp := upperHalfPlane_distinct_isometric_lines_intersection_subsingleton α β hα hβ hne
  have he : α s = α u := hp ⟨⟨t, hst.symm⟩, s, rfl⟩ ⟨⟨v, huv.symm⟩, u, rfl⟩
  exact ⟨hα.injective he, hβ.injective (hst.symm.trans (he.trans huv))⟩

end Markov
