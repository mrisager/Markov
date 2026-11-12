import Markov.InvariantIsometricAxisHyperbolic
import Markov.MetricCircleLengthFromHomotopy

/-! Actual local unit-speed period circles are lifted and normalized to an
actual hyperbolic deck axis. No free-class or homology premise is used. -/
noncomputable section
open Set Topology
open scoped MatrixGroups
namespace Markov

/-- Hyperbolicity is a consequence of the genuine lifted metric and its
positive period, rather than an extra premise on the endpoint deck element. -/
theorem modularTraceQuotientLift_hyperbolic_of_positive_period
    (γ : ℝ → ModularTraceQuotient) (F : ℝ → UpperHalfPlane) (hF : Continuous F)
    (hproj : ∀ t : ℝ, modularTraceQuotientMk (F t) = γ t)
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (γ s) (γ u) = dist s u)
    (P : ℝ) (hP : 0 < P) (hperiod : Function.Periodic γ P)
    (D : modularTraceSubgroup) (hendpoint : F P = D • F 0) :
    2 < |(D.val : IntMatrixTwo).trace| := by
  have ha : ∀ t : ℝ, (D.val : SL(2, ℝ)) • F t = F (t + P) := by
    intro t
    simpa only [← modularInteger_smul_eq_real] using
      modularTraceQuotientLift_deck_action_of_period γ F hF hproj P hperiod D hendpoint t
  have hh := hyperbolic_trace_of_invariant_isometric_axis (D.val : SL(2, ℝ)) F
    (modularTraceQuotientLift_isometry γ F hF hproj hloc) P hP ha
  have ht : Matrix.trace ((D.val : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      (((D.val : IntMatrixTwo).trace : ℤ) : ℝ) := by
    simp [Matrix.trace, Fin.sum_univ_two]
  rw [ht] at hh
  exact_mod_cast hh

/-- Every actual positive locally unit-speed metric circle has a constructed
full-real lift, a literal forward hyperbolic deck element, and an actual
selected-axis phase. Its actual metric period equals the given circle period.
No embedding, free-class, or homology hypothesis is required. -/
theorem modularMetricCircle_axis_normalization
    (L : ℝ) (hL : 0 < L) (q : C(AddCircle L, ModularTraceQuotient))
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (q (s : AddCircle L)) (q (u : AddCircle L)) = dist s u) :
    ∃ (z : UpperHalfPlane) (F : C(ℝ, UpperHalfPlane)) (D : modularTraceSubgroup)
      (hg : 2 < |(D.val : IntMatrixTwo).trace|) (c : ℝ),
      modularTraceQuotientMk z = q 0 ∧ F 0 = z ∧
      (∀ t : ℝ, modularTraceQuotientMk (F t) = q (t : AddCircle L)) ∧
      Isometry F ∧ F L = D • z ∧
      (∀ t : ℝ, D • F t = F (t + L)) ∧
      modularClosedGeodesicPeriod D = L ∧
      (∀ t : ℝ, F t = modularHyperbolicAxis D hg (t + c)) ∧
      (∀ t : ℝ, q (t : AddCircle L) = modularClosedGeodesic D hg (t + c)) := by
  obtain ⟨z, hz⟩ := modularTraceQuotientMk_surjective (q 0)
  obtain ⟨F, hF0, hproj⟩ := modularMetricCircle_real_lift_exists L q z hz
  let γ : C(ℝ, ModularTraceQuotient) :=
    ⟨fun t => q (t : AddCircle L), q.continuous.comp (AddCircle.continuous_mk' L)⟩
  have hperiod : Function.Periodic γ L := by
    intro t
    change q ((t + L : ℝ) : AddCircle L) = q (t : AddCircle L)
    rw [AddCircle.coe_add, AddCircle.coe_period L, add_zero]
  obtain ⟨D, hD⟩ := (modularTraceQuotientMk_eq_iff (F L) z).mp (by
    rw [hproj, hz, AddCircle.coe_period])
  have hend : F L = D • F 0 := by rw [hF0]; exact hD.symm
  have hg := modularTraceQuotientLift_hyperbolic_of_positive_period γ F F.continuous
    hproj hloc L hL hperiod D hend
  have hFi := modularTraceQuotientLift_isometry γ F F.continuous hproj hloc
  have hact := modularTraceQuotientLift_deck_action_of_period γ F F.continuous
    hproj L hperiod D hend
  have hlen := modularTraceQuotientLift_period_eq_translationLength γ F F.continuous
    hproj hloc L hL hperiod D hend
  have hact' : ∀ t : ℝ, D • F t = F (t + modularClosedGeodesicPeriod D) := by
    rw [hlen]
    exact hact
  obtain ⟨c, hc⟩ := modularHyperbolicAxis_eq_of_isometry_equivariant D hg F hFi hact'
  have hphase (t : ℝ) : F t = modularHyperbolicAxis D hg (t + -c) := by
    simpa only [neg_add_cancel_right] using (hc (t + -c)).symm
  refine ⟨z, F, D, hg, -c, hz, hF0, hproj, hFi, hD.symm, hact, hlen, hphase, ?_⟩
  intro t
  rw [← hproj, hphase]
  rfl

/-- The supplied actual full-real lift determines the complete marked
positive-loop class: the original marking reads the inverse forward deck
label under the checked seed conjugation. -/
theorem modularMetricCircle_positiveLoop_marked_of_lift
    (L : ℝ) (q : C(AddCircle L, ModularTraceQuotient))
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0)
    (F : C(ℝ, UpperHalfPlane)) (hF0 : F 0 = z)
    (hproj : ∀ t : ℝ, modularTraceQuotientMk (F t) = q (t : AddCircle L))
    (D : modularTraceSubgroup) (hD : F L = D • z) :
    modularTraceMarkedFundamentalGroupEquiv z (FundamentalGroup.fromPath
      (.mk ((modularMetricCirclePositiveLoop L q).cast hz hz))) =
      modularTraceSeedConjugation D⁻¹ := by
  let η : Path z (D • z) := {
    toFun := fun t => F ((t : ℝ) * L)
    continuous_toFun := F.continuous.comp (continuous_subtype_val.mul continuous_const)
    source' := by simpa using hF0
    target' := by simpa using hD }
  have hpath :
      (((η.map modularTraceQuotientMk_continuous).cast rfl
        (modularTraceQuotientMk_smul D z).symm)) =
      (modularMetricCirclePositiveLoop L q).cast hz hz := by
    ext t
    exact (hproj ((t : ℝ) * L)).trans (modularMetricCirclePositiveLoop_apply L q t).symm
  rw [← hpath]
  exact modularTraceMarkedFundamentalGroupEquiv_projectedPath z D η

end Markov
