import Markov.NormalArcProximity
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Angular bounds imply Euclidean bounds for actual normal sets. The
circle arc containing the normals remains an explicit hypothesis; this
module does not assert a normal-turn tail for cutoff arcs. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace Markov

/-- For unit vectors the Euclidean chord is bounded by the undirected
angle, measured in radians. -/
theorem dist_le_angle_of_norm_eq_one {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (x y : V) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    dist x y ≤ InnerProductGeometry.angle x y := by
  let t := InnerProductGeometry.angle x y
  have ht : 0 ≤ t := InnerProductGeometry.angle_nonneg x y
  have hcos : Real.cos t = ⟪x, y⟫ := by
    simpa [t, hx, hy] using InnerProductGeometry.cos_angle x y
  have hnorm : ‖x - y‖ ^ 2 = 2 - 2 * Real.cos t := by
    rw [norm_sub_sq_real, hx, hy, ← hcos]
    ring
  have hdouble : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    have hc := Real.cos_two_mul (t / 2)
    have hs := Real.sin_sq_add_cos_sq (t / 2)
    have heq : 2 * (t / 2) = t := by ring
    rw [heq] at hc
    nlinarith
  have hs : Real.sin (t / 2) ^ 2 ≤ (t / 2) ^ 2 := Real.sin_sq_le_sq
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (x - y)]

/-- The actual unit circle in the Euclidean coordinate plane. The
parameter is a real angle in radians, rather than a synthetic arc size. -/
def circleNormal (θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![Real.cos θ, Real.sin θ]

@[simp] theorem circleNormal_zero_apply (θ : ℝ) : circleNormal θ 0 = Real.cos θ := rfl

@[simp] theorem circleNormal_one_apply (θ : ℝ) : circleNormal θ 1 = Real.sin θ := rfl

theorem norm_circleNormal (θ : ℝ) : ‖circleNormal θ‖ = 1 := by
  have hsq : ‖circleNormal θ‖ ^ 2 = 1 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs,
      circleNormal]
  nlinarith [norm_nonneg (circleNormal θ)]

/-- Euclidean distance along the unit circle is at most the difference
of its real angle parameters. No restriction to a short arc is needed. -/
theorem dist_circleNormal_le (θ φ : ℝ) : dist (circleNormal θ) (circleNormal φ) ≤ |θ - φ| := by
  have hnorm : ‖circleNormal θ - circleNormal φ‖ ^ 2 =
      (Real.cos θ - Real.cos φ) ^ 2 + (Real.sin θ - Real.sin φ) ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, circleNormal]
  have hcos : Real.cos (θ - φ) =
      Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ := Real.cos_sub θ φ
  have hdouble : Real.cos (θ - φ) = 1 - 2 * Real.sin ((θ - φ) / 2) ^ 2 := by
    have hc := Real.cos_two_mul ((θ - φ) / 2)
    have hs := Real.sin_sq_add_cos_sq ((θ - φ) / 2)
    have heq : 2 * ((θ - φ) / 2) = θ - φ := by ring
    rw [heq] at hc
    nlinarith
  have hs : Real.sin ((θ - φ) / 2) ^ 2 ≤ ((θ - φ) / 2) ^ 2 := Real.sin_sq_le_sq
  have hθ := Real.sin_sq_add_cos_sq θ
  have hφ := Real.sin_sq_add_cos_sq φ
  rw [dist_eq_norm]
  nlinarith [sq_abs (θ - φ), norm_nonneg (circleNormal θ - circleNormal φ),
    abs_nonneg (θ - φ)]

/-- The angle parameterization of the Euclidean unit circle has Lipschitz
constant one. -/
theorem circleNormal_lipschitz : LipschitzWith 1 circleNormal := by
  apply LipschitzWith.mk_one
  intro θ φ
  simpa only [Real.dist_eq] using dist_circleNormal_le θ φ

/-- Two parameters in one real interval have chord distance at most its
angular width. -/
theorem dist_circleNormal_le_angular_width (a b θ φ : ℝ)
    (hθ : θ ∈ Icc a b) (hφ : φ ∈ Icc a b) :
    dist (circleNormal θ) (circleNormal φ) ≤ b - a := by
  apply (dist_circleNormal_le θ φ).trans
  apply abs_le.mpr
  constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2]

/-- A set contained in a parameterized circle arc has Euclidean diameter
at most the angular width of that arc. -/
theorem diam_le_angular_width_of_subset_circleNormal_image
    (S : Set (EuclideanSpace ℝ (Fin 2))) (a b : ℝ) (hab : a ≤ b)
    (harc : S ⊆ circleNormal '' Icc a b) : Metric.diam S ≤ b - a := by
  apply Metric.diam_le_of_forall_dist_le (sub_nonneg.mpr hab)
  intro x hx y hy
  obtain ⟨θ, hθ, rfl⟩ := harc hx
  obtain ⟨φ, hφ, rfl⟩ := harc hy
  exact dist_circleNormal_le_angular_width a b θ φ hθ hφ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Angular containment of the actual support normals supplies the
Euclidean normal-diameter input used in the endpoint transfer. -/
theorem normalsOn_diam_le_angular_width (C : Module.Basis (Fin 2) ℝ E)
    (S : Set E) (a b : ℝ) (hab : a ≤ b)
    (harc : normalsOn C S ⊆ circleNormal '' Icc a b) :
    Metric.diam (normalsOn C S) ≤ b - a :=
  diam_le_angular_width_of_subset_circleNormal_image (normalsOn C S) a b hab harc

/-- A nearby angle parameter of an actual normal supplies a nearby
Euclidean normal; its actual membership remains explicit. -/
theorem exists_normal_near_of_angular_witness (C : Module.Basis (Fin 2) ℝ E)
    (S : Set E) (φ η : ℝ)
    (hnear : ∃ θ, circleNormal θ ∈ normalsOn C S ∧ |θ - φ| ≤ η) :
    ∃ y ∈ normalsOn C S, dist y (circleNormal φ) ≤ η := by
  obtain ⟨θ, hθ, hθφ⟩ := hnear
  exact ⟨circleNormal θ, hθ, (dist_circleNormal_le θ φ).trans hθφ⟩

/-- An angular arc bound and an actual angular witness control every
point in the closure of the actual normal set. -/
theorem normal_dist_le_angular_width_add_of_mem_closure
    (C : Module.Basis (Fin 2) ℝ E) (S : Set E)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ closure (normalsOn C S))
    (a b φ η : ℝ) (hab : a ≤ b)
    (harc : normalsOn C S ⊆ circleNormal '' Icc a b)
    (hnear : ∃ θ, circleNormal θ ∈ normalsOn C S ∧ |θ - φ| ≤ η) :
    dist x (circleNormal φ) ≤ (b - a) + η := by
  exact dist_le_add_of_mem_closure_of_exists_near (normalsOn_isBounded C S) hx
    (b - a) η (normalsOn_diam_le_angular_width C S a b hab harc)
    (exists_normal_near_of_angular_witness C S φ η hnear)

/-- Explicit angular containment and a nearby angular witness transfer
to the selected normal at the endpoint of the actual local boundary arc.
The endpoint's closure membership is already proved in `BoundaryNormals`. -/
theorem selectedSupport_normal_dist_le_angular_width_add
    (B C : Module.Basis (Fin 2) ℝ E) (ε : ℝ) (hε : 0 < ε)
    (a b φ η : ℝ) (hab : a ≤ b)
    (harc : normalsOn C (slopeBoundaryArc B 0 ε) ⊆ circleNormal '' Icc a b)
    (hnear : ∃ θ, circleNormal θ ∈ normalsOn C (slopeBoundaryArc B 0 ε) ∧
      |θ - φ| ≤ η) :
    dist (normalizedEuclideanCovector C (selectedSupport B)) (circleNormal φ) ≤
      (b - a) + η := by
  exact selectedSupport_normal_dist_le_add B C ε hε (circleNormal φ) (b - a) η
    (normalsOn_diam_le_angular_width C (slopeBoundaryArc B 0 ε) a b hab harc)
    (exists_normal_near_of_angular_witness C (slopeBoundaryArc B 0 ε) φ η hnear)

end Markov
