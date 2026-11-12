import Markov.FareyRefinement
import Markov.FareyFanLocal
import Markov.FrickeLengthTriangle

/-! Actual canonical trace-length interpolants on finite Farey edges.
Mediant subdivision decreases the interpolant on each child cone, by the
proved strict local Fricke triangle inequality. No norm or compatibility
hypothesis is used. -/

noncomputable section

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual homogeneous linear interpolant on a matrix-carrying edge. -/
def fareyEdgeInterpolant (B : Module.Basis (Fin 2) ℝ E) (e : FareyEdge) : E →ₗ[ℝ] ℝ :=
  pairInterpolant B e.u e.v (by rw [e.holonomy.det_eq_one]; norm_num)
    (primitiveFareyLength e.u e.holonomy.left_nonnegativePrimitive)
    (primitiveFareyLength e.v e.holonomy.right_nonnegativePrimitive)

theorem fareyEdgeInterpolant_left (B : Module.Basis (Fin 2) ℝ E) (e : FareyEdge) :
    fareyEdgeInterpolant B e (intVector B e.u) =
      primitiveFareyLength e.u e.holonomy.left_nonnegativePrimitive := by
  exact pairInterpolant_left _ _ _ _ _ _

theorem fareyEdgeInterpolant_right (B : Module.Basis (Fin 2) ℝ E) (e : FareyEdge) :
    fareyEdgeInterpolant B e (intVector B e.v) =
      primitiveFareyLength e.v e.holonomy.right_nonnegativePrimitive := by
  exact pairInterpolant_right _ _ _ _ _ _

theorem fareyEdgeInterpolant_sum (B : Module.Basis (Fin 2) ℝ E) (e : FareyEdge) :
    fareyEdgeInterpolant B e (intVector B (e.u + e.v)) =
      primitiveFareyLength e.u e.holonomy.left_nonnegativePrimitive +
        primitiveFareyLength e.v e.holonomy.right_nonnegativePrimitive := by
  rw [intVector_add, map_add, fareyEdgeInterpolant_left, fareyEdgeInterpolant_right]

/-- The new mediant ray strictly lowers the left child's interpolant. -/
theorem fareyEdgeInterpolant_left_newray_lt (B : Module.Basis (Fin 2) ℝ E) (e : FareyEdge) :
    fareyEdgeInterpolant B e.left (intVector B (e.u + e.v)) <
      fareyEdgeInterpolant B e (intVector B (e.u + e.v)) := by
  have hc := fareyEdgeInterpolant_right B e.left
  change fareyEdgeInterpolant B e.left (intVector B (e.u + e.v)) =
    primitiveFareyLength (e.u + e.v) e.left.holonomy.right_nonnegativePrimitive at hc
  rw [hc, fareyEdgeInterpolant_sum]
  exact e.holonomy.canonicalLength_strict_triangle e.holonomy.left_nonnegativePrimitive
    e.holonomy.right_nonnegativePrimitive e.left.holonomy.right_nonnegativePrimitive

/-- The same strict decrease on the new ray for the right child. -/
theorem fareyEdgeInterpolant_right_newray_lt (B : Module.Basis (Fin 2) ℝ E) (e : FareyEdge) :
    fareyEdgeInterpolant B e.right (intVector B (e.u + e.v)) <
      fareyEdgeInterpolant B e (intVector B (e.u + e.v)) := by
  have hc := fareyEdgeInterpolant_left B e.right
  change fareyEdgeInterpolant B e.right (intVector B (e.u + e.v)) =
    primitiveFareyLength (e.u + e.v) e.right.holonomy.left_nonnegativePrimitive at hc
  rw [hc, fareyEdgeInterpolant_sum]
  exact e.holonomy.canonicalLength_strict_triangle e.holonomy.left_nonnegativePrimitive
    e.holonomy.right_nonnegativePrimitive e.right.holonomy.left_nonnegativePrimitive

/-- Refinement decreases the interpolation throughout the actual left cone. -/
theorem fareyEdgeInterpolant_left_le (B : Module.Basis (Fin 2) ℝ E) (e : FareyEdge)
    (x : E) (hx : x ∈ twoRayCone (intVector B e.u) (intVector B (e.u + e.v))) :
    fareyEdgeInterpolant B e.left x ≤ fareyEdgeInterpolant B e x := by
  apply linearMap_le_on_twoRayCone _ _ (intVector B e.u) (intVector B (e.u + e.v)) _ _ x hx
  · exact (fareyEdgeInterpolant_left B e.left).trans (fareyEdgeInterpolant_left B e).symm
  · exact (fareyEdgeInterpolant_left_newray_lt B e).le

/-- Refinement decreases the interpolation throughout the actual right cone. -/
theorem fareyEdgeInterpolant_right_le (B : Module.Basis (Fin 2) ℝ E) (e : FareyEdge)
    (x : E) (hx : x ∈ twoRayCone (intVector B (e.u + e.v)) (intVector B e.v)) :
    fareyEdgeInterpolant B e.right x ≤ fareyEdgeInterpolant B e x := by
  have hx' : x ∈ twoRayCone (intVector B e.v) (intVector B (e.u + e.v)) := by
    rcases hx with ⟨a, b, ha, hb, rfl⟩
    exact ⟨b, a, hb, ha, add_comm _ _⟩
  apply linearMap_le_on_twoRayCone _ _ (intVector B e.v) (intVector B (e.u + e.v)) _ _ x hx'
  · exact (fareyEdgeInterpolant_right B e.right).trans (fareyEdgeInterpolant_right B e).symm
  · exact (fareyEdgeInterpolant_right_newray_lt B e).le

/-- Strict decrease whenever the mediant coefficient is positive on the
left child; in particular this holds in its relative interior. -/
theorem fareyEdgeInterpolant_left_lt (B : Module.Basis (Fin 2) ℝ E) (e : FareyEdge)
    (a b : ℝ) (hb : 0 < b) :
    fareyEdgeInterpolant B e.left (a • intVector B e.u + b • intVector B (e.u + e.v)) <
      fareyEdgeInterpolant B e (a • intVector B e.u + b • intVector B (e.u + e.v)) := by
  have hu : fareyEdgeInterpolant B e.left (intVector B e.u) =
      fareyEdgeInterpolant B e (intVector B e.u) :=
    (fareyEdgeInterpolant_left B e.left).trans (fareyEdgeInterpolant_left B e).symm
  simp only [map_add, map_smul, smul_eq_mul, hu]
  have hh := mul_lt_mul_of_pos_left (fareyEdgeInterpolant_left_newray_lt B e) hb
  linarith

/-- The corresponding strict decrease on the right child. -/
theorem fareyEdgeInterpolant_right_lt (B : Module.Basis (Fin 2) ℝ E) (e : FareyEdge)
    (a b : ℝ) (ha : 0 < a) :
    fareyEdgeInterpolant B e.right (a • intVector B (e.u + e.v) + b • intVector B e.v) <
      fareyEdgeInterpolant B e (a • intVector B (e.u + e.v) + b • intVector B e.v) := by
  have hv : fareyEdgeInterpolant B e.right (intVector B e.v) =
      fareyEdgeInterpolant B e (intVector B e.v) :=
    (fareyEdgeInterpolant_right B e.right).trans (fareyEdgeInterpolant_right B e).symm
  simp only [map_add, map_smul, smul_eq_mul, hv]
  have hh := mul_lt_mul_of_pos_left (fareyEdgeInterpolant_right_newray_lt B e) ha
  linarith

/-- Uniform child-edge form of the one-step decrease, suited to frontier
refinement and its actual child-cone membership. -/
theorem fareyEdgeInterpolant_refine_le (B : Module.Basis (Fin 2) ℝ E)
    (e child : FareyEdge) (hchild : child ∈ e.refine) (x : E)
    (hx : x ∈ twoRayCone (intVector B child.u) (intVector B child.v)) :
    fareyEdgeInterpolant B child x ≤ fareyEdgeInterpolant B e x := by
  simp [FareyEdge.refine] at hchild
  rcases hchild with rfl | rfl
  · exact fareyEdgeInterpolant_left_le B e x hx
  · exact fareyEdgeInterpolant_right_le B e x hx

end Markov
