import Markov.UpperHalfPlaneCayleyEndpoints
import Markov.HyperbolicAxisMinset
import Markov.EquivariantCurveAxisBounds
import Markov.CanonicalProperEmbeddedLift

noncomputable section
open Filter Set Topology
open scoped MatrixGroups
namespace Markov

/-- An actual positive diagonal action coordinate bounds every continuous
unit-equivariant curve against the explicit positive-speed vertical line. -/
theorem hyperbolicEquivariantCurve_normalized_uniform_distance
    (g : SL(2, ℝ)) (a : ℝ) (ha : 1 < a) (h : SL(2, ℝ))
    (hact : ∀ z : UpperHalfPlane, g • z =
      h • (hyperbolicPositiveDiagonal a (by linarith) • (h⁻¹ • z)))
    (F : ℝ → UpperHalfPlane) (hcF : Continuous F)
    (hF : ∀ t, F (t+1) = g • F t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t,
      dist (h⁻¹ • F t) (hyperbolicVerticalAxis ((2*Real.log a)*t)) ≤ B := by
  apply equivariant_curves_uniform_distance
    (fun z => hyperbolicPositiveDiagonal a (by linarith) • z)
    (isometry_smul UpperHalfPlane (hyperbolicPositiveDiagonal a (by linarith)))
    (fun t => h⁻¹ • F t) (fun t => hyperbolicVerticalAxis ((2*Real.log a)*t))
    1 (by norm_num)
  · exact (isometry_smul UpperHalfPlane h⁻¹).continuous.comp hcF
  · exact hyperbolicVerticalAxis_isometry.continuous.comp
      (continuous_const.mul continuous_id)
  · intro t
    rw [hF t, hact (F t), inv_smul_smul]
  · intro t
    rw [hyperbolicPositiveDiagonal_axis_action]
    congr 1
    ring

/-- Hyperbolicity alone supplies an actual SL coordinate, actual uniform
vertical bound, and both actual complex Cayley limits for an equivariant curve. -/
theorem hyperbolicEquivariantCurve_has_normalized_cayley_endpoints
    (g : SL(2, ℝ)) (hg : 2 < |(g : Matrix (Fin 2) (Fin 2) ℝ).trace|)
    (F : ℝ → UpperHalfPlane) (hcF : Continuous F)
    (hF : ∀ t, F (t+1) = g • F t) :
    ∃ a : ℝ, ∃ ha : 1 < a, ∃ h : SL(2, ℝ), ∃ B : ℝ,
      (∀ z : UpperHalfPlane, g • z =
        h • (hyperbolicPositiveDiagonal a (by linarith) • (h⁻¹ • z))) ∧
      hyperbolicTranslationLength g = 2*Real.log a ∧ 0 ≤ B ∧
      (∀ t, dist (h⁻¹ • F t) (hyperbolicVerticalAxis ((2*Real.log a)*t)) ≤ B) ∧
      Tendsto (fun t => upperHalfPlaneCayley (h⁻¹ • F t)) atBot (𝓝 (-1 : ℂ)) ∧
      Tendsto (fun t => upperHalfPlaneCayley (h⁻¹ • F t)) atTop (𝓝 (1 : ℂ)) := by
  obtain ⟨a, ha, h, hact, hlen⟩ :=
    exists_hyperbolicPositiveDiagonal_action_conjugacy g hg
  obtain ⟨B, hB, hbound⟩ :=
    hyperbolicEquivariantCurve_normalized_uniform_distance g a ha h hact F hcF hF
  have hk : 0 < 2*Real.log a := mul_pos (by norm_num) (Real.log_pos ha)
  exact ⟨a, ha, h, B, hact, hlen, hB, hbound,
    upperHalfPlaneCayley_tendsto_atBot_of_dist_vertical
      (fun t => h⁻¹ • F t) (2*Real.log a) B hk hbound,
    upperHalfPlaneCayley_tendsto_atTop_of_dist_vertical
      (fun t => h⁻¹ • F t) (2*Real.log a) B hk hbound⟩

/-- The same actual coordinate and endpoints for a literal modular deck curve,
with its actual metric period retained. -/
theorem modularEquivariantCurve_has_normalized_cayley_endpoints
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (F : ℝ → UpperHalfPlane) (hcF : Continuous F)
    (hF : ∀ t, F (t+1) = g • F t) :
    ∃ a : ℝ, ∃ ha : 1 < a, ∃ h : SL(2, ℝ), ∃ B : ℝ,
      (∀ z : UpperHalfPlane, (g.val : SL(2, ℝ)) • z =
        h • (hyperbolicPositiveDiagonal a (by linarith) • (h⁻¹ • z))) ∧
      modularClosedGeodesicPeriod g = 2*Real.log a ∧ 0 ≤ B ∧
      (∀ t, dist (h⁻¹ • F t) (hyperbolicVerticalAxis ((2*Real.log a)*t)) ≤ B) ∧
      Tendsto (fun t => upperHalfPlaneCayley (h⁻¹ • F t)) atBot (𝓝 (-1 : ℂ)) ∧
      Tendsto (fun t => upperHalfPlaneCayley (h⁻¹ • F t)) atTop (𝓝 (1 : ℂ)) := by
  have ht : ((g.val : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
      ((g.val : IntMatrixTwo).trace : ℝ) := by
    simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  have hgr : 2 < |((g.val : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace| := by
    rw [ht]
    exact_mod_cast hg
  apply hyperbolicEquivariantCurve_has_normalized_cayley_endpoints
    (g.val : SL(2, ℝ)) hgr F hcF
  intro t
  rw [hF t]
  exact modularInteger_smul_eq_real g.val (F t)

/-- The actual canonical proper embedded full-real lift has a genuine
SL-normalized pair of complex endpoints, with its literal monodromy retained. -/
theorem paperPrimitiveHolonomy_has_properEmbeddedLift_cayley_endpoints
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    ∃ (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
      (d : Path paperGeneratorCenterPoint (q 0)),
      embeddedCircleConnectorDeck q hq d = paperPrimitiveHolonomy k p hp ∧
      IsProperMap (embeddedCircleConnectorRealLift q hq d) ∧
      IsClosedEmbedding (embeddedCircleConnectorRealLift q hq d) ∧
      (∀ t : ℝ, embeddedCircleConnectorRealLift q hq d (t+1) =
        paperPrimitiveHolonomy k p hp • embeddedCircleConnectorRealLift q hq d t) ∧
      ∃ a : ℝ, ∃ ha : 1 < a, ∃ h : SL(2, ℝ), ∃ B : ℝ,
        (∀ z : UpperHalfPlane, ((paperPrimitiveHolonomy k p hp).val : SL(2, ℝ)) • z =
          h • (hyperbolicPositiveDiagonal a (by linarith) • (h⁻¹ • z))) ∧
        modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hp) = 2*Real.log a ∧
        0 ≤ B ∧
        (∀ t, dist (h⁻¹ • embeddedCircleConnectorRealLift q hq d t)
          (hyperbolicVerticalAxis ((2*Real.log a)*t)) ≤ B) ∧
        Tendsto (fun t => upperHalfPlaneCayley
          (h⁻¹ • embeddedCircleConnectorRealLift q hq d t)) atBot (𝓝 (-1 : ℂ)) ∧
        Tendsto (fun t => upperHalfPlaneCayley
          (h⁻¹ • embeddedCircleConnectorRealLift q hq d t)) atTop (𝓝 (1 : ℂ)) := by
  obtain ⟨q, hq, d, hD, hproper, hemb, hunit, _⟩ :=
    paperPrimitiveHolonomy_has_properEmbeddedLift k p hp
  refine ⟨q, hq, d, hD, hproper, hemb, hunit, ?_⟩
  exact modularEquivariantCurve_has_normalized_cayley_endpoints
    (paperPrimitiveHolonomy k p hp) (paperPrimitiveHolonomy_hyperbolic k p hp)
    (embeddedCircleConnectorRealLift q hq d)
    (embeddedCircleConnectorRealLift q hq d).continuous hunit

end Markov
