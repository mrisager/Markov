import Markov.NormalDeterminant
import Markov.AngularNormals
import Markov.UnimodularPartners
import Mathlib.Analysis.Real.Pi.Bounds

/-! Distinct primitive integral directions of Euclidean size at most `T`
are separated by angle at least `1 / T²`. The determinant estimate gives
this spacing for independent directions. Bezout and the unimodular kernel
identity reduce dependent primitive directions to equality or opposition.
This is an angular-spacing ingredient, not the full Lemma 7. -/

noncomputable section
namespace Markov

/-- A primitive integral pair cannot be the zero direction. -/
theorem primitiveIntDirection_ne_zero (d : ℤ × ℤ) (hd : IsCoprime d.1 d.2) :
    d ≠ (0, 0) := by
  intro hzero
  rw [hzero] at hd
  norm_num at hd

/-- The integral determinant is bounded by the product of the original
Euclidean lengths and the angle of the normalized original directions. -/
theorem intDet_abs_le_norm_mul_angle (d e : ℤ × ℤ)
    (hd : d ≠ (0, 0)) (he : e ≠ (0, 0)) :
    |(intDet d e : ℝ)| ≤ intEuclidean d * intEuclidean e *
      InnerProductGeometry.angle (NormedSpace.normalize (euclideanIntDirection d))
        (NormedSpace.normalize (euclideanIntDirection e)) := by
  have hdet := euclideanPlaneDet_abs_le_normal_distance
    (euclideanIntDirection d) (euclideanIntDirection e) (euclideanIntDirection_ne_zero e he)
  have heval : euclideanPlaneDet (euclideanIntDirection d) (euclideanIntDirection e) =
      (intDet d e : ℝ) := by
    simp [euclideanPlaneDet, euclideanIntDirection, intDet]
  rw [heval, euclideanIntDirection_norm, euclideanIntDirection_norm] at hdet
  exact hdet.trans (mul_le_mul_of_nonneg_left
    (dist_le_angle_of_norm_eq_one _ _
      (NormedSpace.norm_normalize (euclideanIntDirection_ne_zero d hd))
      (NormedSpace.norm_normalize (euclideanIntDirection_ne_zero e he)))
    (mul_nonneg (intEuclidean_nonneg d) (intEuclidean_nonneg e)))

/-- Dependent primitive integral directions are equal or opposite. The
coefficient supplied by the unimodular kernel identity is an integer unit. -/
theorem primitive_intDet_zero_eq_or_eq_neg (d e : ℤ × ℤ)
    (hd : IsCoprime d.1 d.2) (he : IsCoprime e.1 e.2) (hdet : intDet d e = 0) :
    e = d ∨ e = -d := by
  obtain ⟨s, t, hbezout⟩ := hd
  let w : ℤ × ℤ := (-t, s)
  have hpartner : intDet d w = 1 := by
    dsimp [intDet, w]
    nlinarith only [hbezout]
  let k : ℤ := intDet e w
  have hmultiple : e = k • d := unimodular_kernel_eq_zsmul d w e hpartner hdet
  have hkfirst : k ∣ e.1 := by
    refine ⟨d.1, ?_⟩
    have h := congrArg Prod.fst hmultiple
    simpa only [Prod.smul_fst, zsmul_eq_mul] using h
  have hksecond : k ∣ e.2 := by
    refine ⟨d.2, ?_⟩
    have h := congrArg Prod.snd hmultiple
    simpa only [Prod.smul_snd, zsmul_eq_mul] using h
  have hkunit : IsUnit k := he.isUnit_of_dvd' hkfirst hksecond
  rcases Int.isUnit_iff.mp hkunit with hk | hk
  · left
    simpa only [hk, one_smul] using hmultiple
  · right
    simpa only [hk, neg_one_smul] using hmultiple

@[simp] theorem euclideanIntDirection_neg (d : ℤ × ℤ) :
    euclideanIntDirection (-d) = -euclideanIntDirection d := by
  ext i
  fin_cases i <;> simp [euclideanIntDirection]

/-- Distinct primitive directions of length at most `T` have angular
spacing at least `1 / T²`, including the opposite-direction case. -/
theorem primitive_angular_spacing (d e : ℤ × ℤ)
    (hd : IsCoprime d.1 d.2) (he : IsCoprime e.1 e.2) (hne : d ≠ e)
    (T : ℝ) (hT : 1 ≤ T) (hdT : intEuclidean d ≤ T) (heT : intEuclidean e ≤ T) :
    1 / T ^ 2 ≤
      InnerProductGeometry.angle (NormedSpace.normalize (euclideanIntDirection d))
        (NormedSpace.normalize (euclideanIntDirection e)) := by
  have hdne := primitiveIntDirection_ne_zero d hd
  have hene := primitiveIntDirection_ne_zero e he
  have hTpos : 0 < T := by linarith
  have hTtwo : 0 < T ^ 2 := sq_pos_of_pos hTpos
  by_cases hdet : intDet d e = 0
  · rcases primitive_intDet_zero_eq_or_eq_neg d e hd he hdet with heq | heq
    · exact (hne heq.symm).elim
    · have hangle :
          InnerProductGeometry.angle (NormedSpace.normalize (euclideanIntDirection d))
            (NormedSpace.normalize (euclideanIntDirection e)) = Real.pi := by
        rw [InnerProductGeometry.angle_normalize_left, InnerProductGeometry.angle_normalize_right,
          heq, euclideanIntDirection_neg,
          InnerProductGeometry.angle_self_neg_of_nonzero (euclideanIntDirection_ne_zero d hdne)]
      rw [hangle]
      have hunit : 1 / T ^ 2 ≤ 1 := (div_le_one hTtwo).mpr (by nlinarith)
      exact hunit.trans (by linarith [Real.pi_gt_three])
  · have hdetlower : (1 : ℝ) ≤ |(intDet d e : ℝ)| := by
      have hint : (1 : ℤ) ≤ |intDet d e| := Int.one_le_abs hdet
      exact_mod_cast hint
    have hdetupper := intDet_abs_le_norm_mul_angle d e hdne hene
    have hproduct : intEuclidean d * intEuclidean e ≤ T ^ 2 := by
      calc
        intEuclidean d * intEuclidean e ≤ T * T :=
          mul_le_mul hdT heT (intEuclidean_nonneg e) hTpos.le
        _ = T ^ 2 := by ring
    have hbound := hdetlower.trans (hdetupper.trans
      (mul_le_mul_of_nonneg_right hproduct (InnerProductGeometry.angle_nonneg _ _)))
    apply (div_le_iff₀ hTtwo).mpr
    simpa only [mul_comm] using hbound

/-- Two primitive directions under the same length bound are equal if
their angular distance is strictly smaller than the spacing threshold. -/
theorem primitive_eq_of_angle_lt_inv_sq (d e : ℤ × ℤ)
    (hd : IsCoprime d.1 d.2) (he : IsCoprime e.1 e.2)
    (T : ℝ) (hT : 1 ≤ T) (hdT : intEuclidean d ≤ T) (heT : intEuclidean e ≤ T)
    (hangle : InnerProductGeometry.angle (NormedSpace.normalize (euclideanIntDirection d))
      (NormedSpace.normalize (euclideanIntDirection e)) < 1 / T ^ 2) : d = e := by
  by_contra hne
  exact (not_lt_of_ge (primitive_angular_spacing d e hd he hne T hT hdT heT)) hangle

end Markov
