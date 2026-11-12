import Markov.CircularNormalSeparation
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Every unit vector has a real angle lift at exactly its circular
distance from any specified real base angle. In particular, taking a
closed angular neighborhood of a compact circle arc enlarges its real
parameter interval by the same radius, including across the circle seam. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace Markov

/-- A unit circle vector admits a lift whose distance from a prescribed
real angle is exactly the ordinary angle between the corresponding
vectors. The principal argument is taken after rotating the base vector
to angle zero, so no cut at a fixed circle seam is involved. -/
theorem exists_circleNormal_eq_and_abs_sub_eq_angle
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1) (φ : ℝ) :
    ∃ ψ : ℝ, z = circleNormal ψ ∧
      |ψ - φ| = InnerProductGeometry.angle (circleNormal φ) z := by
  have hzsq : z 0 ^ 2 + z 1 ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) hz
    simpa [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs] using h
  let w : ℂ := ⟨Real.cos φ * z 0 + Real.sin φ * z 1,
    Real.cos φ * z 1 - Real.sin φ * z 0⟩
  have hw : ‖w‖ = 1 := by
    have hw_sq : ‖w‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      dsimp [w]
      calc
        _ = (Real.sin φ ^ 2 + Real.cos φ ^ 2) * (z 0 ^ 2 + z 1 ^ 2) := by ring
        _ = 1 := by rw [Real.sin_sq_add_cos_sq, hzsq, one_mul]
    nlinarith [norm_nonneg w]
  have hwne : w ≠ 0 := by
    intro h
    simp [h] at hw
  have hcos : Real.cos w.arg = Real.cos φ * z 0 + Real.sin φ * z 1 := by
    simpa [hw, w] using Complex.cos_arg hwne
  have hsin : Real.sin w.arg = Real.cos φ * z 1 - Real.sin φ * z 0 := by
    simpa [hw, w] using Complex.sin_arg w
  have heq : z = circleNormal (φ + w.arg) := by
    ext i
    fin_cases i
    · change z 0 = Real.cos (φ + w.arg)
      rw [Real.cos_add, hcos, hsin]
      symm
      calc
        _ = (Real.sin φ ^ 2 + Real.cos φ ^ 2) * z 0 := by ring
        _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]
    · change z 1 = Real.sin (φ + w.arg)
      rw [Real.sin_add, hcos, hsin]
      symm
      calc
        _ = (Real.sin φ ^ 2 + Real.cos φ ^ 2) * z 1 := by ring
        _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]
  refine ⟨φ + w.arg, heq, ?_⟩
  rw [heq, angle_circleNormal_eq_arccos_cos_sub]
  have hsub : φ + w.arg - φ = w.arg := by ring
  rw [hsub, ← Real.cos_abs w.arg,
    Real.arccos_cos (abs_nonneg w.arg) (Complex.abs_arg_le_pi w)]

/-- Every unit vector in the Euclidean coordinate plane is a circle
normal with a real angle parameter. -/
theorem exists_circleNormal_eq_of_norm_eq_one
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1) :
    ∃ ψ : ℝ, z = circleNormal ψ := by
  obtain ⟨ψ, hψ, _⟩ := exists_circleNormal_eq_and_abs_sub_eq_angle z hz 0
  exact ⟨ψ, hψ⟩

/-- An ordinary angular bound has a real lift with exactly the same
radius. No upper bound on the radius, or restriction away from a seam,
is needed. -/
theorem exists_circleNormal_eq_and_abs_sub_le_of_angle_le
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1) (φ η : ℝ)
    (hangle : InnerProductGeometry.angle (circleNormal φ) z ≤ η) :
    ∃ ψ : ℝ, z = circleNormal ψ ∧ |ψ - φ| ≤ η := by
  obtain ⟨ψ, hψ, hdist⟩ := exists_circleNormal_eq_and_abs_sub_eq_angle z hz φ
  exact ⟨ψ, hψ, hdist.trans_le hangle⟩

/-- The real circle image of a closed bounded interval is closed. -/
theorem isClosed_circleNormal_image_Icc (a b : ℝ) :
    IsClosed (circleNormal '' Icc a b) :=
  (isCompact_Icc.image circleNormal_lipschitz.continuous).isClosed

/-- The same enlarged-interval lift holds for the closed angular
neighborhood of any nonempty actual set contained in the circle arc.
The angular witness may be attained only in the closure of that set. -/
theorem exists_mem_Icc_eq_circleNormal_of_mem_closedAngularNeighborhood_of_subset
    (J : Set (EuclideanSpace ℝ (Fin 2))) (hJ : J.Nonempty)
    (a b η : ℝ) (harc : J ⊆ circleNormal '' Icc a b)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ closedAngularNeighborhood J η) :
    ∃ ψ ∈ Icc (a - η) (b + η), z = circleNormal ψ := by
  have hunit : ∀ y ∈ J, ‖y‖ = 1 := by
    intro y hy
    obtain ⟨θ, _, rfl⟩ := harc hy
    exact norm_circleNormal θ
  obtain ⟨hzunit, y, hy, hangle⟩ :=
    (mem_closedAngularNeighborhood_iff_exists_mem_closure J hJ hunit z η).mp hz
  have hyarc : y ∈ circleNormal '' Icc a b :=
    closure_minimal harc (isClosed_circleNormal_image_Icc a b) hy
  obtain ⟨φ, hφ, rfl⟩ := hyarc
  obtain ⟨ψ, hψ, hnear⟩ :=
    exists_circleNormal_eq_and_abs_sub_le_of_angle_le z hzunit φ η hangle
  refine ⟨ψ, ?_, hψ⟩
  have hnear' := abs_le.mp hnear
  constructor <;> linarith [hφ.1, hφ.2, hnear'.1, hnear'.2]

/-- A closed angular neighborhood of a compact circle arc is contained
in the image of the interval enlarged by the same angular radius. -/
theorem exists_mem_Icc_eq_circleNormal_of_mem_closedAngularNeighborhood
    (a b η : ℝ) (hab : a ≤ b) (z : EuclideanSpace ℝ (Fin 2))
    (hz : z ∈ closedAngularNeighborhood (circleNormal '' Icc a b) η) :
    ∃ ψ ∈ Icc (a - η) (b + η), z = circleNormal ψ := by
  have hJ : (circleNormal '' Icc a b).Nonempty :=
    ⟨circleNormal a, ⟨a, ⟨le_rfl, hab⟩, rfl⟩⟩
  exact exists_mem_Icc_eq_circleNormal_of_mem_closedAngularNeighborhood_of_subset
    (circleNormal '' Icc a b) hJ a b η Subset.rfl z hz

end Markov
