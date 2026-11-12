import Markov.HyperbolicTranslationLength

/-! Literal phase and range transport under one actual SL chart. These are
action identities, not an assumption about endpoint separation or simplicity. -/

noncomputable section
open Set
open scoped MatrixGroups
namespace Markov

private theorem axisRange_phase (f : ℝ → UpperHalfPlane) (c : ℝ) :
    Set.range (fun t => f (t + c)) = Set.range f := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t + c, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t - c, by simp only [sub_add_cancel]⟩

/-- The actual translated axis in one inverse chart, with phase retained. -/
theorem hyperbolicAxis_chart_translate_apply
    (A d : SL(2, ℝ)) (α : ℝ → UpperHalfPlane) (c : ℝ)
    (hα : ∀ t : ℝ, α t = A • hyperbolicVerticalAxis (t + c)) (t : ℝ) :
    A⁻¹ • (d • α t) = (A⁻¹ * d * A) • hyperbolicVerticalAxis (t + c) := by
  rw [hα t]
  simp only [mul_smul]

/-- Exact point-intersection equivalence including both real parameter shifts. -/
theorem hyperbolicAxis_chart_point_eq_iff
    (A d : SL(2, ℝ)) (α : ℝ → UpperHalfPlane) (c : ℝ)
    (hα : ∀ t : ℝ, α t = A • hyperbolicVerticalAxis (t + c)) (s t : ℝ) :
    d • α s = α t ↔
      (A⁻¹ * d * A) • hyperbolicVerticalAxis (s + c) = hyperbolicVerticalAxis (t + c) := by
  constructor
  · intro he
    have hh := congrArg (fun z : UpperHalfPlane => A⁻¹ • z) he
    dsimp only at hh
    rw [hyperbolicAxis_chart_translate_apply A d α c hα, hα t, inv_smul_smul] at hh
    exact hh
  · intro he
    have hh := congrArg (fun z : UpperHalfPlane => A • z) he
    simp only [mul_smul, smul_inv_smul] at hh
    rw [hα s, hα t]
    exact hh

/-- The inverse chart sends the entire actual selected-axis range to the
literal vertical range; the phase is removed by an explicit parameter shift. -/
theorem hyperbolicAxis_chart_range
    (A : SL(2, ℝ)) (α : ℝ → UpperHalfPlane) (c : ℝ)
    (hα : ∀ t : ℝ, α t = A • hyperbolicVerticalAxis (t + c)) :
    (fun z : UpperHalfPlane => A⁻¹ • z) '' Set.range α = Set.range hyperbolicVerticalAxis := by
  rw [← Set.range_comp']
  have he : (fun t : ℝ => A⁻¹ • α t) = fun t => hyperbolicVerticalAxis (t + c) := by
    funext t
    rw [hα t, inv_smul_smul]
  rw [he]
  exact axisRange_phase hyperbolicVerticalAxis c

/-- The same inverse chart sends an actual d-translated axis range to the
literal range for the actual conjugate A^-1*d*A. -/
theorem hyperbolicAxis_chart_translate_range
    (A d : SL(2, ℝ)) (α : ℝ → UpperHalfPlane) (c : ℝ)
    (hα : ∀ t : ℝ, α t = A • hyperbolicVerticalAxis (t + c)) :
    (fun z : UpperHalfPlane => A⁻¹ • z) '' Set.range (fun t : ℝ => d • α t) =
      Set.range (fun t : ℝ => (A⁻¹ * d * A) • hyperbolicVerticalAxis t) := by
  rw [← Set.range_comp']
  have he : (fun t : ℝ => A⁻¹ • (d • α t)) =
      fun t => (A⁻¹ * d * A) • hyperbolicVerticalAxis (t + c) := by
    funext t
    exact hyperbolicAxis_chart_translate_apply A d α c hα t
  rw [he]
  exact axisRange_phase (fun t => (A⁻¹ * d * A) • hyperbolicVerticalAxis t) c

/-- Actual equality of the original axis ranges is equivalent to actual
equality of the two literal normalized ranges. -/
theorem hyperbolicAxis_chart_range_eq_iff
    (A d : SL(2, ℝ)) (α : ℝ → UpperHalfPlane) (c : ℝ)
    (hα : ∀ t : ℝ, α t = A • hyperbolicVerticalAxis (t + c)) :
    Set.range (fun t : ℝ => d • α t) = Set.range α ↔
      Set.range (fun t : ℝ => (A⁻¹ * d * A) • hyperbolicVerticalAxis t) =
        Set.range hyperbolicVerticalAxis := by
  have he := Set.image_eq_image (f := fun z : UpperHalfPlane => A⁻¹ • z)
    (s := Set.range (fun t : ℝ => d • α t)) (t := Set.range α)
    (isometry_smul UpperHalfPlane A⁻¹).injective
  rw [hyperbolicAxis_chart_translate_range A d α c hα,
    hyperbolicAxis_chart_range A α c hα] at he
  exact he.symm

/-- Exact disjointness transport under the actual inverse chart. -/
theorem hyperbolicAxis_chart_ranges_disjoint_iff
    (A d : SL(2, ℝ)) (α : ℝ → UpperHalfPlane) (c : ℝ)
    (hα : ∀ t : ℝ, α t = A • hyperbolicVerticalAxis (t + c)) :
    Disjoint (Set.range (fun t : ℝ => d • α t)) (Set.range α) ↔
      Disjoint (Set.range (fun t : ℝ => (A⁻¹ * d * A) • hyperbolicVerticalAxis t))
        (Set.range hyperbolicVerticalAxis) := by
  have he := Set.disjoint_image_iff (f := fun z : UpperHalfPlane => A⁻¹ • z)
    (s := Set.range (fun t : ℝ => d • α t)) (t := Set.range α)
    (isometry_smul UpperHalfPlane A⁻¹).injective
  rw [hyperbolicAxis_chart_translate_range A d α c hα,
    hyperbolicAxis_chart_range A α c hα] at he
  exact he.symm

/-- Exact existence-of-intersection transport, with the actual relative SL
matrix and phase-compatible witnesses supplied by the preceding point iff. -/
theorem hyperbolicAxis_chart_ranges_intersect_iff
    (A d : SL(2, ℝ)) (α : ℝ → UpperHalfPlane) (c : ℝ)
    (hα : ∀ t : ℝ, α t = A • hyperbolicVerticalAxis (t + c)) :
    (Set.range (fun t : ℝ => d • α t) ∩ Set.range α).Nonempty ↔
      (Set.range (fun t : ℝ => (A⁻¹ * d * A) • hyperbolicVerticalAxis t) ∩
        Set.range hyperbolicVerticalAxis).Nonempty := by
  simpa only [disjoint_iff_inter_eq_empty, Set.nonempty_iff_ne_empty] using
    not_congr (hyperbolicAxis_chart_ranges_disjoint_iff A d α c hα)

end Markov
