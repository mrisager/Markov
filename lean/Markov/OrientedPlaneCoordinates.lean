import Markov.EuclideanPairCoordinates
import Markov.CircleNormalOffsets

/-! Volume-preserving coordinates along a unit normal and its positive quarter
turn. These coordinates use the standard Euclidean volume throughout. -/

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace Markov

private theorem orientedPlane_orthonormal (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1) :
    Orthonormal ℝ ![θ, quarterTurnNormal θ] := by
  have he : ‖quarterTurnNormal θ‖ = 1 := by rw [norm_quarterTurnNormal, hθ]
  have ho : inner ℝ θ (quarterTurnNormal θ) = 0 := inner_quarterTurnNormal_self θ
  have ho' : inner ℝ (quarterTurnNormal θ) θ = 0 := by rw [real_inner_comm]; exact ho
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hθ, he, ho, ho']

/-- The oriented orthonormal basis determined by a unit normal. -/
def orientedPlaneBasis (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1) :
    OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  OrthonormalBasis.mk (orientedPlane_orthonormal θ hθ)
    ((orientedPlane_orthonormal θ hθ).linearIndependent.span_eq_top_of_card_eq_finrank
      (by simp)).ge

@[simp] theorem orientedPlaneBasis_zero (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1) :
    orientedPlaneBasis θ hθ 0 = θ := by
  exact congrFun (OrthonormalBasis.coe_mk (orientedPlane_orthonormal θ hθ) _) 0

@[simp] theorem orientedPlaneBasis_one (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1) :
    orientedPlaneBasis θ hθ 1 = quarterTurnNormal θ := by
  exact congrFun (OrthonormalBasis.coe_mk (orientedPlane_orthonormal θ hθ) _) 1

/-- The Euclidean linear isometry sending the standard basis to the normal
and its positive quarter turn. -/
def orientedPlaneRotation (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1) :
    EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (orientedPlaneBasis θ hθ).repr.symm

theorem orientedPlaneRotation_apply (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1)
    (z : EuclideanSpace ℝ (Fin 2)) :
    orientedPlaneRotation θ hθ z = z 0 • θ + z 1 • quarterTurnNormal θ := by
  simpa only [Fin.sum_univ_two, orientedPlaneBasis_zero, orientedPlaneBasis_one] using
    ((orientedPlaneBasis θ hθ).sum_repr_symm z).symm

/-- The volume-preserving oriented pair coordinates `(t,s) ↦ tθ + sJθ`. -/
def orientedPlaneCoordinates (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1) :
    (ℝ × ℝ) ≃ᵐ EuclideanSpace ℝ (Fin 2) :=
  euclideanPairEquiv.trans (orientedPlaneRotation θ hθ).toHomeomorph.toMeasurableEquiv

/-- The same oriented coordinate map as a continuous linear equivalence. -/
def orientedPlaneContinuousLinearEquiv (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1) :
    (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  euclideanPairContinuousLinearEquiv.trans (orientedPlaneRotation θ hθ).toContinuousLinearEquiv

@[simp] theorem orientedPlaneContinuousLinearEquiv_apply
    (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1) (p : ℝ × ℝ) :
    orientedPlaneContinuousLinearEquiv θ hθ p = orientedPlaneCoordinates θ hθ p := rfl

@[simp] theorem orientedPlaneCoordinates_apply (θ : EuclideanSpace ℝ (Fin 2))
    (hθ : ‖θ‖ = 1) (p : ℝ × ℝ) :
    orientedPlaneCoordinates θ hθ p = p.1 • θ + p.2 • quarterTurnNormal θ := by
  exact orientedPlaneRotation_apply θ hθ (euclideanPairEquiv p)

theorem orientedPlaneCoordinates_measurePreserving (θ : EuclideanSpace ℝ (Fin 2))
    (hθ : ‖θ‖ = 1) : MeasurePreserving (orientedPlaneCoordinates θ hθ) :=
  (orientedPlaneRotation θ hθ).measurePreserving.comp euclideanPairEquiv_measurePreserving

theorem orientedPlaneCoordinates_continuous (θ : EuclideanSpace ℝ (Fin 2))
    (hθ : ‖θ‖ = 1) : Continuous (orientedPlaneCoordinates θ hθ) :=
  (orientedPlaneContinuousLinearEquiv θ hθ).continuous

theorem orientedPlaneCoordinates_symm_continuous (θ : EuclideanSpace ℝ (Fin 2))
    (hθ : ‖θ‖ = 1) : Continuous (orientedPlaneCoordinates θ hθ).symm :=
  (orientedPlaneContinuousLinearEquiv θ hθ).symm.continuous

theorem orientedPlaneCoordinates_contDiff (θ : EuclideanSpace ℝ (Fin 2))
    (hθ : ‖θ‖ = 1) : ContDiff ℝ ∞ (orientedPlaneCoordinates θ hθ) :=
  (orientedPlaneContinuousLinearEquiv θ hθ).contDiff

theorem orientedPlaneCoordinates_symm_contDiff (θ : EuclideanSpace ℝ (Fin 2))
    (hθ : ‖θ‖ = 1) : ContDiff ℝ ∞ (orientedPlaneCoordinates θ hθ).symm :=
  (orientedPlaneContinuousLinearEquiv θ hθ).symm.contDiff

theorem orientedPlaneCoordinates_isClosedEmbedding (θ : EuclideanSpace ℝ (Fin 2))
    (hθ : ‖θ‖ = 1) : Topology.IsClosedEmbedding (orientedPlaneCoordinates θ hθ) :=
  (orientedPlaneContinuousLinearEquiv θ hθ).toHomeomorph.isClosedEmbedding

theorem orientedPlaneCoordinates_norm_sq (θ : EuclideanSpace ℝ (Fin 2))
    (hθ : ‖θ‖ = 1) (p : ℝ × ℝ) :
    ‖orientedPlaneCoordinates θ hθ p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  change ‖orientedPlaneRotation θ hθ (euclideanPairEquiv p)‖ ^ 2 = _
  rw [(orientedPlaneRotation θ hθ).norm_map, euclideanPairEquiv_norm_sq]

theorem orientedPlaneCoordinates_inner (θ : EuclideanSpace ℝ (Fin 2))
    (hθ : ‖θ‖ = 1) (p q : ℝ × ℝ) :
    inner ℝ (orientedPlaneCoordinates θ hθ p) (orientedPlaneCoordinates θ hθ q) =
      p.1 * q.1 + p.2 * q.2 := by
  change inner ℝ (orientedPlaneRotation θ hθ (euclideanPairEquiv p))
    (orientedPlaneRotation θ hθ (euclideanPairEquiv q)) = _
  rw [(orientedPlaneRotation θ hθ).inner_map_map, euclideanPairEquiv_inner]

@[simp] theorem orientedPlaneCoordinates_inner_normal (θ : EuclideanSpace ℝ (Fin 2))
    (hθ : ‖θ‖ = 1) (p : ℝ × ℝ) :
    inner ℝ (orientedPlaneCoordinates θ hθ p) θ = p.1 := by
  have ho : inner ℝ (quarterTurnNormal θ) θ = 0 := by
    rw [real_inner_comm]
    exact inner_quarterTurnNormal_self θ
  simp only [orientedPlaneCoordinates_apply, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hθ, one_pow, mul_one, ho, mul_zero, add_zero]

@[simp] theorem orientedPlaneCoordinates_inner_transverse (θ : EuclideanSpace ℝ (Fin 2))
    (hθ : ‖θ‖ = 1) (p : ℝ × ℝ) :
    inner ℝ (orientedPlaneCoordinates θ hθ p) (quarterTurnNormal θ) = p.2 := by
  simp only [orientedPlaneCoordinates_apply, inner_add_left, real_inner_smul_left,
    inner_quarterTurnNormal_self, real_inner_self_eq_norm_sq, norm_quarterTurnNormal,
    hθ, one_pow, mul_one, mul_zero, zero_add]

theorem orientedPlaneCoordinates_inner_smul_normal (θ : EuclideanSpace ℝ (Fin 2))
    (hθ : ‖θ‖ = 1) (p : ℝ × ℝ) (r : ℝ) :
    inner ℝ (orientedPlaneCoordinates θ hθ p) (r • θ) = r * p.1 := by
  rw [inner_smul_right, orientedPlaneCoordinates_inner_normal]

theorem orientedPlaneCoordinates_symm_apply (θ : EuclideanSpace ℝ (Fin 2))
    (hθ : ‖θ‖ = 1) (z : EuclideanSpace ℝ (Fin 2)) :
    (orientedPlaneCoordinates θ hθ).symm z =
      (inner ℝ z θ, inner ℝ z (quarterTurnNormal θ)) := by
  obtain ⟨p, rfl⟩ := (orientedPlaneCoordinates θ hθ).surjective z
  simp only [MeasurableEquiv.symm_apply_apply, orientedPlaneCoordinates_inner_normal,
    orientedPlaneCoordinates_inner_transverse]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact change to oriented coordinates, with no Jacobian or volume factor. -/
theorem integral_orientedPlaneCoordinates (θ : EuclideanSpace ℝ (Fin 2)) (hθ : ‖θ‖ = 1)
    (f : EuclideanSpace ℝ (Fin 2) → E) :
    (∫ z, f z) = ∫ p : ℝ × ℝ, f (orientedPlaneCoordinates θ hθ p) :=
  ((orientedPlaneCoordinates_measurePreserving θ hθ).integral_comp' f).symm

/-- Fubini along an arbitrary unit normal and its positive quarter turn. -/
theorem integral_orientedPlaneCoordinates_double (θ : EuclideanSpace ℝ (Fin 2))
    (hθ : ‖θ‖ = 1) (f : EuclideanSpace ℝ (Fin 2) → E) (hf : Integrable f) :
    (∫ z, f z) = ∫ t : ℝ, ∫ s : ℝ, f (t • θ + s • quarterTurnNormal θ) := by
  rw [integral_orientedPlaneCoordinates θ hθ]
  have hi : Integrable (fun p : ℝ × ℝ => f (orientedPlaneCoordinates θ hθ p)) :=
    ((orientedPlaneCoordinates_measurePreserving θ hθ).integrable_comp_emb
      (orientedPlaneCoordinates θ hθ).measurableEmbedding).mpr hf
  simpa only [orientedPlaneCoordinates_apply] using integral_prod _ hi

end Markov
