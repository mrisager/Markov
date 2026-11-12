import Markov.TraceBoundaryAtoms
import Markov.NormalDeterminant

/-! A determinant of two genuine norming supports gives a lower bound
for the actual boundary turn atom. The full normal fibre identifies the
angular interval between their normalized normals with part of that atom. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Markov

/-- Every pair of genuine normals over a boundary point is separated by
at most the angular length of its actual boundary turn atom. -/
theorem traceBoundaryTurn_normal_distance_le (x : TracePlane) (hx : ‖x‖ = 1)
    (f g : StrongDual ℝ TracePlane)
    (hf : f ∈ normingFunctionals x) (hg : g ∈ normingFunctionals x) :
    dist (normalizedEuclideanCovector traceBasis f)
      (normalizedEuclideanCovector traceBasis g) ≤ (traceBoundaryTurn {x}).toReal := by
  obtain ⟨a, b, hab, harc, hmass⟩ := traceBoundaryTurn_full_normal_fibre x hx
  have hfn : normalizedEuclideanCovector traceBasis f ∈ normalsOn traceBasis {x} :=
    ⟨x, rfl, f, hf, rfl⟩
  have hgn : normalizedEuclideanCovector traceBasis g ∈ normalsOn traceBasis {x} :=
    ⟨x, rfl, g, hg, rfl⟩
  rw [harc] at hfn hgn
  obtain ⟨θ, hθ, hθf⟩ := hfn
  obtain ⟨φ, hφ, hφg⟩ := hgn
  rw [hmass, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab), ← hθf, ← hφg]
  exact dist_circleNormal_le_angular_width a b θ φ hθ hφ

/-- The determinant of any two actual norming supports is bounded by a
fixed coordinate constant times the actual boundary atom, without any
extremality assumption on the supports. -/
theorem traceBoundaryTurn_det_le (x : TracePlane) (hx : ‖x‖ = 1)
    (f g : StrongDual ℝ TracePlane)
    (hf : f ∈ normingFunctionals x) (hg : g ∈ normingFunctionals x) :
    |euclideanPlaneDet (euclideanDualCoordinates traceBasis f)
      (euclideanDualCoordinates traceBasis g)| ≤
      (‖traceBasis 0‖ + ‖traceBasis 1‖) ^ 2 * (traceBoundaryTurn {x}).toReal := by
  have hxne : x ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  have hgne := euclideanDualCoordinates_ne_zero traceBasis g
    (normingFunctional_ne_zero x hxne g hg)
  have hnorm : ‖euclideanDualCoordinates traceBasis f‖ *
      ‖euclideanDualCoordinates traceBasis g‖ ≤ (‖traceBasis 0‖ + ‖traceBasis 1‖) ^ 2 := by
    simpa only [pow_two] using mul_le_mul
      (euclideanDualCoordinates_norm_le traceBasis f hf.1)
      (euclideanDualCoordinates_norm_le traceBasis g hg.1)
      (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
  apply (euclideanPlaneDet_abs_le_normal_distance _ _ hgne).trans
  calc
    ‖euclideanDualCoordinates traceBasis f‖ * ‖euclideanDualCoordinates traceBasis g‖ *
        dist (NormedSpace.normalize (euclideanDualCoordinates traceBasis f))
          (NormedSpace.normalize (euclideanDualCoordinates traceBasis g)) ≤
        (‖traceBasis 0‖ + ‖traceBasis 1‖) ^ 2 *
          dist (normalizedEuclideanCovector traceBasis f)
            (normalizedEuclideanCovector traceBasis g) :=
      mul_le_mul_of_nonneg_right hnorm dist_nonneg
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (traceBoundaryTurn_normal_distance_le x hx f g hf hg) (sq_nonneg _)

theorem traceBasis_norm_sum_pos : 0 < ‖traceBasis 0‖ + ‖traceBasis 1‖ :=
  add_pos_of_pos_of_nonneg (norm_pos_iff.mpr (traceBasis.ne_zero 0)) (norm_nonneg _)

/-- A pair of genuine norming supports supplies a quantitative lower
bound for the actual boundary atom through its coordinate determinant. -/
theorem traceBoundaryTurn_atom_lower_of_norming_det (x : TracePlane) (hx : ‖x‖ = 1)
    (f g : StrongDual ℝ TracePlane)
    (hf : f ∈ normingFunctionals x) (hg : g ∈ normingFunctionals x) :
    |euclideanPlaneDet (euclideanDualCoordinates traceBasis f)
      (euclideanDualCoordinates traceBasis g)| / (‖traceBasis 0‖ + ‖traceBasis 1‖) ^ 2 ≤
      (traceBoundaryTurn {x}).toReal := by
  apply (div_le_iff₀ (sq_pos_of_pos traceBasis_norm_sum_pos)).mpr
  simpa only [mul_comm] using traceBoundaryTurn_det_le x hx f g hf hg

end Markov
