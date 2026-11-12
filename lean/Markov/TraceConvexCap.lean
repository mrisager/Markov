import Markov.TraceEuclideanSupport
import Markov.EuclideanCapBracket

/-! Spatial estimates for caps of the actual trace unit ball. The two
supporting points remain associated with their explicit actual normals. -/

noncomputable section
open Set
namespace Markov

/-- The actual cap cut from the Euclidean image of the trace unit ball by
the supporting line at depth `δ` in direction `z`. -/
def traceConvexCap (z : EuclideanSpace ℝ (Fin 2)) (δ : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {p ∈ traceEuclideanBall | traceEuclideanSupportHeight z - δ ≤ inner ℝ p z}

theorem traceConvexCap_inner_bounds (z : EuclideanSpace ℝ (Fin 2)) (δ : ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ traceConvexCap z δ) :
    traceEuclideanSupportHeight z - δ ≤ inner ℝ p z ∧
      inner ℝ p z ≤ traceEuclideanSupportHeight z :=
  ⟨hp.2, inner_le_traceEuclideanSupportHeight z p hp.1⟩

/-- Projection onto the cap direction varies by at most its actual depth. -/
theorem traceConvexCap_longitudinal_width
    (z : EuclideanSpace ℝ (Fin 2)) (δ : ℝ) (_hδ : 0 ≤ δ)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ traceConvexCap z δ)
    (q : EuclideanSpace ℝ (Fin 2)) (hq : q ∈ traceConvexCap z δ) :
    |inner ℝ (p - q) z| ≤ δ := by
  obtain ⟨hplo, hphi⟩ := traceConvexCap_inner_bounds z δ p hp
  obtain ⟨hqlo, hqhi⟩ := traceConvexCap_inner_bounds z δ q hq
  rw [inner_sub_left, abs_le]
  constructor <;> linarith

/-- Every point of the original unit ball, whether or not it supports the
cap direction, gives the depth lower bound needed by the cap bracket. -/
theorem traceConvexCap_depth
    (z : EuclideanSpace ℝ (Fin 2)) (δ : ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ traceConvexCap z δ)
    (x : TracePlane) (hx : ‖x‖ ≤ 1) :
    -δ ≤ inner ℝ (p - traceEuclideanCoordinates x) z := by
  have hupper := inner_le_traceEuclideanSupportHeight z (traceEuclideanCoordinates x)
    (traceEuclideanCoordinates_mem_ball x hx)
  rw [inner_sub_left]
  linarith [hp.2]

/-- The actual trace cap satisfies the trigonometric spatial bound when
its two endpoint points carry the indicated actual support normals. -/
theorem traceConvexCap_diam_le_trigonometric
    (z e : EuclideanSpace ℝ (Fin 2)) (xMinus xPlus : TracePlane) (δ η : ℝ)
    (hz : ‖z‖ = 1) (he : ‖e‖ = 1) (horth : inner ℝ z e = 0)
    (hxMinus : ‖xMinus‖ = 1) (hxPlus : ‖xPlus‖ = 1)
    (hδ : 0 ≤ δ) (hη : 0 < η) (hηhalf : η < Real.pi / 2)
    (hminus : Real.cos η • z - Real.sin η • e ∈ normalsOn traceBasis {xMinus})
    (hplus : Real.cos η • z + Real.sin η • e ∈ normalsOn traceBasis {xPlus}) :
    Metric.diam (traceConvexCap z δ) ≤
      dist (traceEuclideanCoordinates xMinus) (traceEuclideanCoordinates xPlus) +
        2 * δ * (Real.cos η / Real.sin η) + δ := by
  have hsPlus := (traceEuclideanBall_support_of_mem_normalsOn_singleton
    xPlus hxPlus _ hplus).2.2
  have hsMinus := (traceEuclideanBall_support_of_mem_normalsOn_singleton
    xMinus hxMinus _ hminus).2.2
  have hc : 0 ≤ Real.cos η := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hηhalf⟩).le
  have hs : 0 < Real.sin η := Real.sin_pos_of_pos_of_lt_pi hη
    (by linarith [Real.pi_pos])
  apply euclideanCap_diam_le (traceConvexCap z δ) z e
    (traceEuclideanCoordinates xMinus) (traceEuclideanCoordinates xPlus)
    δ (Real.cos η) (Real.sin η) hz he horth hδ hc hs
  · intro p hp
    exact hsPlus p hp.1
  · intro p hp
    exact hsMinus p hp.1
  · intro p hp
    exact traceConvexCap_depth z δ p hp xPlus hxPlus.le
  · intro p hp
    exact traceConvexCap_depth z δ p hp xMinus hxMinus.le
  · exact traceConvexCap_longitudinal_width z δ hδ

/-- On the positive half-quadrant the cotangent is bounded by the
elementary linear lower estimate for sine. -/
theorem cos_div_sin_le_pi_div_two_mul (η : ℝ) (hη : 0 < η)
    (hηhalf : η < Real.pi / 2) :
    Real.cos η / Real.sin η ≤ Real.pi / (2 * η) := by
  have hs : 0 < Real.sin η := Real.sin_pos_of_pos_of_lt_pi hη
    (by linarith [Real.pi_pos])
  have hsin := Real.mul_le_sin hη.le hηhalf.le
  have hp : 2 * η ≤ Real.pi * Real.sin η := by
    have hh := mul_le_mul_of_nonneg_left hsin Real.pi_pos.le
    convert hh using 1
    field_simp
  apply (div_le_div_iff₀ hs (mul_pos (by norm_num) hη)).mpr
  nlinarith [Real.cos_le_one η]

/-- The two transverse bracket errors and longitudinal depth are bounded
by one universal multiple of `δ / η`. -/
theorem trigonometric_cap_error_le (δ η : ℝ) (hδ : 0 ≤ δ) (hη : 0 < η)
    (hηhalf : η < Real.pi / 2) :
    2 * δ * (Real.cos η / Real.sin η) + δ ≤ 2 * Real.pi * δ / η := by
  have hcot := mul_le_mul_of_nonneg_left
    (cos_div_sin_le_pi_div_two_mul η hη hηhalf) (show 0 ≤ 2 * δ by positivity)
  have hdepth : δ ≤ Real.pi * δ / η := by
    apply (le_div_iff₀ hη).mpr
    have hηpi : η ≤ Real.pi := by linarith [Real.pi_pos]
    nlinarith
  calc
    2 * δ * (Real.cos η / Real.sin η) + δ ≤
        2 * δ * (Real.pi / (2 * η)) + Real.pi * δ / η := add_le_add hcot hdepth
    _ = 2 * Real.pi * δ / η := by ring

/-- The actual trace cap has diameter at most the endpoint separation
plus the uniform cap error. -/
theorem traceConvexCap_diam_le
    (z e : EuclideanSpace ℝ (Fin 2)) (xMinus xPlus : TracePlane) (δ η : ℝ)
    (hz : ‖z‖ = 1) (he : ‖e‖ = 1) (horth : inner ℝ z e = 0)
    (hxMinus : ‖xMinus‖ = 1) (hxPlus : ‖xPlus‖ = 1)
    (hδ : 0 ≤ δ) (hη : 0 < η) (hηhalf : η < Real.pi / 2)
    (hminus : Real.cos η • z - Real.sin η • e ∈ normalsOn traceBasis {xMinus})
    (hplus : Real.cos η • z + Real.sin η • e ∈ normalsOn traceBasis {xPlus}) :
    Metric.diam (traceConvexCap z δ) ≤
      dist (traceEuclideanCoordinates xMinus) (traceEuclideanCoordinates xPlus) +
        2 * Real.pi * δ / η := by
  have h := traceConvexCap_diam_le_trigonometric z e xMinus xPlus δ η
    hz he horth hxMinus hxPlus hδ hη hηhalf hminus hplus
  have herr := trigonometric_cap_error_le δ η hδ hη hηhalf
  linarith

/-- Any established bound for the actual endpoint separation transfers
directly to the diameter of the actual trace cap. -/
theorem traceConvexCap_diam_le_of_dist_le
    (z e : EuclideanSpace ℝ (Fin 2)) (xMinus xPlus : TracePlane) (δ η s : ℝ)
    (hz : ‖z‖ = 1) (he : ‖e‖ = 1) (horth : inner ℝ z e = 0)
    (hxMinus : ‖xMinus‖ = 1) (hxPlus : ‖xPlus‖ = 1)
    (hδ : 0 ≤ δ) (hη : 0 < η) (hηhalf : η < Real.pi / 2)
    (hminus : Real.cos η • z - Real.sin η • e ∈ normalsOn traceBasis {xMinus})
    (hplus : Real.cos η • z + Real.sin η • e ∈ normalsOn traceBasis {xPlus})
    (hdist : dist (traceEuclideanCoordinates xMinus) (traceEuclideanCoordinates xPlus) ≤ s) :
    Metric.diam (traceConvexCap z δ) ≤ s + 2 * Real.pi * δ / η :=
  (traceConvexCap_diam_le z e xMinus xPlus δ η hz he horth hxMinus hxPlus
    hδ hη hηhalf hminus hplus).trans (add_le_add hdist le_rfl)

end Markov
