import Markov.ClosedAngularNeighborhood
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-! Angular separation of closed normal neighborhoods and of circular
images of ordered real intervals. Both directions around the circle are
controlled, so separation is retained across the angle-parameter seam. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace Markov

/-- Thickening two unit-normal sets by the same angular radius reduces
their proved closure separation by at most twice that radius. -/
theorem closedAngularNeighborhood_angle_separation
    (J J' : Set (EuclideanSpace ℝ (Fin 2)))
    (hJ : J.Nonempty) (hJ' : J'.Nonempty)
    (hunit : ∀ y ∈ J, ‖y‖ = 1) (hunit' : ∀ y ∈ J', ‖y‖ = 1)
    (δ η : ℝ)
    (hsep : ∀ y ∈ closure J, ∀ y' ∈ closure J',
      δ ≤ InnerProductGeometry.angle y y')
    (z z' : EuclideanSpace ℝ (Fin 2))
    (hz : z ∈ closedAngularNeighborhood J η)
    (hz' : z' ∈ closedAngularNeighborhood J' η) :
    δ - 2 * η ≤ InnerProductGeometry.angle z z' := by
  obtain ⟨_, y, hy, hyz⟩ :=
    (mem_closedAngularNeighborhood_iff_exists_mem_closure J hJ hunit z η).mp hz
  obtain ⟨_, y', hy', hyz'⟩ :=
    (mem_closedAngularNeighborhood_iff_exists_mem_closure J' hJ' hunit' z' η).mp hz'
  have hfirst := InnerProductGeometry.angle_le_angle_add_angle y z y'
  have hsecond := InnerProductGeometry.angle_le_angle_add_angle z z' y'
  rw [InnerProductGeometry.angle_comm z' y'] at hsecond
  linarith [hsep y hy y' hy']

/-- Closed angular neighborhoods are disjoint when their radius is less
than half the angular separation of the two normal closures. -/
theorem disjoint_closedAngularNeighborhood_of_angle_separation
    (J J' : Set (EuclideanSpace ℝ (Fin 2)))
    (hJ : J.Nonempty) (hJ' : J'.Nonempty)
    (hunit : ∀ y ∈ J, ‖y‖ = 1) (hunit' : ∀ y ∈ J', ‖y‖ = 1)
    (δ η : ℝ)
    (hsep : ∀ y ∈ closure J, ∀ y' ∈ closure J',
      δ ≤ InnerProductGeometry.angle y y') (hη : 2 * η < δ) :
    Disjoint (closedAngularNeighborhood J η) (closedAngularNeighborhood J' η) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have h := closedAngularNeighborhood_angle_separation
    J J' hJ hJ' hunit hunit' δ η hsep z z hz hz'
  have hz0 : z ≠ 0 := by
    intro heq
    have := hz.1
    simp [heq] at this
  rw [InnerProductGeometry.angle_self hz0] at h
  linarith

/-- The angle between two circle normals is the inverse cosine of the
cosine of the difference of their real parameters. -/
theorem angle_circleNormal_eq_arccos_cos_sub (θ φ : ℝ) :
    InnerProductGeometry.angle (circleNormal θ) (circleNormal φ) =
      Real.arccos (Real.cos (φ - θ)) := by
  have hinner : ⟪circleNormal θ, circleNormal φ⟫ = Real.cos (φ - θ) := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, circleNormal_zero_apply,
      circleNormal_one_apply, RCLike.inner_apply,
      conj_trivial]
    rw [Real.cos_sub]
  rw [InnerProductGeometry.angle, norm_circleNormal, norm_circleNormal, one_mul,
    div_one, hinner]

/-- On one positive traversal the ordinary angle is the smaller of the
two directed circular differences. -/
theorem angle_circleNormal_eq_min_of_ordered
    (θ φ : ℝ) (horder : θ ≤ φ) (hperiod : φ ≤ θ + 2 * Real.pi) :
    InnerProductGeometry.angle (circleNormal θ) (circleNormal φ) =
      min (φ - θ) (2 * Real.pi - (φ - θ)) := by
  rw [angle_circleNormal_eq_arccos_cos_sub]
  by_cases hshort : φ - θ ≤ Real.pi
  · rw [Real.arccos_cos (by linarith) hshort, min_eq_left (by linarith)]
  · have hnonneg : 0 ≤ 2 * Real.pi - (φ - θ) := by linarith
    have hle : 2 * Real.pi - (φ - θ) ≤ Real.pi := by linarith
    rw [← Real.cos_two_pi_sub (φ - θ), Real.arccos_cos hnonneg hle,
      min_eq_right (by linarith)]

/-- Two ordered angle intervals have the lower angular separation given
by lower bounds for both the forward gap and the wrapped gap. -/
theorem angle_circleNormal_ge_of_interval_separation
    (α β γ ζ δ θ φ : ℝ)
    (_hαβ : α ≤ β) (hβγ : β ≤ γ) (_hγζ : γ ≤ ζ)
    (hperiod : ζ ≤ α + 2 * Real.pi)
    (hforward : δ ≤ γ - β) (hwrapped : δ ≤ α + 2 * Real.pi - ζ)
    (hθ : θ ∈ Icc α β) (hφ : φ ∈ Icc γ ζ) :
    δ ≤ InnerProductGeometry.angle (circleNormal θ) (circleNormal φ) := by
  rw [angle_circleNormal_eq_min_of_ordered θ φ (by linarith [hθ.2, hφ.1])
    (by linarith [hθ.1, hφ.2])]
  apply le_min
  · linarith [hθ.2, hφ.1]
  · linarith [hθ.1, hφ.2]

end Markov
