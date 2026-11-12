import Markov.NormalArcClosure
import Markov.TraceSeparation

/-! Euclidean normal proximity gives the determinant upper estimate used
in v1 Lemma 6. Proximity of the actual cutoff normal arcs remains an input;
no normal-turn tail is asserted here. -/

noncomputable section
namespace Markov

def euclideanPlaneDet (a b : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  a 0 * b 1 - a 1 * b 0

theorem euclideanPlaneDet_smul_left (r : ℝ) (a b : EuclideanSpace ℝ (Fin 2)) :
    euclideanPlaneDet (r • a) b = r * euclideanPlaneDet a b := by
  simp [euclideanPlaneDet]
  ring

theorem euclideanPlaneDet_smul_right (r : ℝ) (a b : EuclideanSpace ℝ (Fin 2)) :
    euclideanPlaneDet a (r • b) = r * euclideanPlaneDet a b := by
  simp [euclideanPlaneDet]
  ring

theorem euclideanPlaneDet_sub_self_right (a b : EuclideanSpace ℝ (Fin 2)) :
    euclideanPlaneDet (a - b) b = euclideanPlaneDet a b := by
  simp [euclideanPlaneDet]
  ring

theorem euclideanPlaneDet_abs_le (a b : EuclideanSpace ℝ (Fin 2)) :
    |euclideanPlaneDet a b| ≤ ‖a‖ * ‖b‖ := by
  have ha : ‖a‖ ^ 2 = (a 0) ^ 2 + (a 1) ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs]
  have hb : ‖b‖ ^ 2 = (b 0) ^ 2 + (b 1) ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs]
  have hid : ‖a‖ ^ 2 * ‖b‖ ^ 2 - euclideanPlaneDet a b ^ 2 =
      (a 0 * b 0 + a 1 * b 1) ^ 2 := by rw [ha, hb]; dsimp [euclideanPlaneDet]; ring
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg a) (norm_nonneg b))).mp
  rw [sq_abs, mul_pow]
  nlinarith [sq_nonneg (a 0 * b 0 + a 1 * b 1)]

theorem euclideanPlaneDet_abs_le_normal_distance (a b : EuclideanSpace ℝ (Fin 2))
    (hb : b ≠ 0) :
    |euclideanPlaneDet a b| ≤ ‖a‖ * ‖b‖ *
      dist (NormedSpace.normalize a) (NormedSpace.normalize b) := by
  have he : euclideanPlaneDet a b = ‖a‖ * ‖b‖ *
      euclideanPlaneDet (NormedSpace.normalize a) (NormedSpace.normalize b) := by
    calc
      euclideanPlaneDet a b = euclideanPlaneDet (‖a‖ • NormedSpace.normalize a)
          (‖b‖ • NormedSpace.normalize b) := by simp only [NormedSpace.norm_smul_normalize]
      _ = _ := by rw [euclideanPlaneDet_smul_left, euclideanPlaneDet_smul_right]; ring
  rw [he, abs_mul, abs_of_nonneg (mul_nonneg (norm_nonneg a) (norm_nonneg b)), dist_eq_norm]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg a) (norm_nonneg b))
  calc
    |euclideanPlaneDet (NormedSpace.normalize a) (NormedSpace.normalize b)| =
        |euclideanPlaneDet (NormedSpace.normalize a - NormedSpace.normalize b)
          (NormedSpace.normalize b)| := by rw [euclideanPlaneDet_sub_self_right]
    _ ≤ ‖NormedSpace.normalize a - NormedSpace.normalize b‖ * ‖NormedSpace.normalize b‖ :=
      euclideanPlaneDet_abs_le _ _
    _ = _ := by rw [NormedSpace.norm_normalize hb, mul_one]

def euclideanIntDirection (d : ℤ × ℤ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(d.1 : ℝ), (d.2 : ℝ)]

theorem euclideanIntDirection_norm (d : ℤ × ℤ) : ‖euclideanIntDirection d‖ = intEuclidean d := by
  simp [euclideanIntDirection, intEuclidean, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    Real.norm_eq_abs]

theorem euclideanIntDirection_ne_zero (d : ℤ × ℤ) (hd : d ≠ (0, 0)) :
    euclideanIntDirection d ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h
  have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) h
  simp [euclideanIntDirection] at h0 h1
  exact hd (Prod.ext h0 h1)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem euclideanDualCoordinates_norm_le (B : Module.Basis (Fin 2) ℝ E)
    (f : StrongDual ℝ E) (hf : ‖f‖ ≤ 1) :
    ‖euclideanDualCoordinates B f‖ ≤ ‖B 0‖ + ‖B 1‖ := by
  have h0 : |f (B 0)| ≤ ‖B 0‖ := (f.le_opNorm _).trans
    (by simpa using mul_le_mul_of_nonneg_right hf (norm_nonneg (B 0)))
  have h1 : |f (B 1)| ≤ ‖B 1‖ := (f.le_opNorm _).trans
    (by simpa using mul_le_mul_of_nonneg_right hf (norm_nonneg (B 1)))
  have hs : ‖euclideanDualCoordinates B f‖ ^ 2 = f (B 0) ^ 2 + f (B 1) ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs]
  have h0s := (sq_le_sq₀ (abs_nonneg (f (B 0))) (norm_nonneg (B 0))).mpr h0
  have h1s := (sq_le_sq₀ (abs_nonneg (f (B 1))) (norm_nonneg (B 1))).mpr h1
  rw [sq_abs] at h0s h1s
  nlinarith [norm_nonneg (euclideanDualCoordinates B f), norm_nonneg (B 0), norm_nonneg (B 1)]

theorem integralCovectorDet_le_normal_distance (B : Module.Basis (Fin 2) ℝ E)
    (f : StrongDual ℝ E) (hf : ‖f‖ ≤ 1) (d : ℤ × ℤ) (hd : d ≠ (0, 0)) :
    |integralCovectorDet (dualCoordinates B f) d| ≤
      (‖B 0‖ + ‖B 1‖) * intEuclidean d *
        dist (normalizedEuclideanCovector B f) (NormedSpace.normalize (euclideanIntDirection d)) := by
  have h := euclideanPlaneDet_abs_le_normal_distance (euclideanDualCoordinates B f)
    (euclideanIntDirection d) (euclideanIntDirection_ne_zero d hd)
  change |integralCovectorDet (dualCoordinates B f) d| ≤ _ at h
  rw [euclideanIntDirection_norm] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  exact mul_le_mul_of_nonneg_right (euclideanDualCoordinates_norm_le B f hf)
    (intEuclidean_nonneg d)

/-- The analytic determinant bound now follows from an explicit geometric
normal-proximity estimate. No determinant upper bound is assumed. -/
theorem selectedSupportAt_det_upper_of_normal_proximity (B : Module.Basis (Fin 2) ℝ E)
    (u v d : ℤ × ℤ) (hdet : intDet u v ≠ 0) (hd : d ≠ (0, 0)) (R c H : ℝ)
    (hnear : dist (normalizedEuclideanCovector B (selectedSupportAt B u v))
      (NormedSpace.normalize (euclideanIntDirection d)) ≤ R * Real.exp (-c * H)) :
    |integralCovectorDet (dualCoordinates B (selectedSupportAt B u v)) d| ≤
      ((‖B 0‖ + ‖B 1‖) * R) * intEuclidean d * Real.exp (-c * H) := by
  apply (integralCovectorDet_le_normal_distance B _
    (selectedSupportAt_spec B u v hdet).1.1 d hd).trans
  calc
    (‖B 0‖ + ‖B 1‖) * intEuclidean d *
        dist (normalizedEuclideanCovector B (selectedSupportAt B u v))
          (NormedSpace.normalize (euclideanIntDirection d)) ≤
        (‖B 0‖ + ‖B 1‖) * intEuclidean d * (R * Real.exp (-c * H)) :=
      mul_le_mul_of_nonneg_left hnear
        (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (intEuclidean_nonneg d))
    _ = _ := by ring

end Markov
