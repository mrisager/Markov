import Markov.TraceUnresolvedSizes
import Markov.TraceUnresolvedUnique

/-! The v1 Lemma 6 estimate for the trace ball, including the
unique association to an unresolved component. Arc size is measured
by Euclidean variation of the radial curve. -/

noncomputable section
open Set
namespace Markov

/-- Uniform real-cutoff Lemma 6 estimates for the unique actual unresolved
component of the constructed trace ball. All exponential diameter, endpoint
support and error-rate inputs have been discharged. The remaining parameter
assumptions are exactly the positive parameters and basic inequality. -/
theorem trace_lemma6 :
    ∃ Ch Ca : ℝ, 0 < Ch ∧ 0 < Ca ∧
      ∀ (K H ε η : ℝ), 1 ≤ H → 0 < ε → 0 < η →
      (2 + ε) * η ≤ traceCornerLowerConstant *
        Real.exp (-(2 * traceAxisLength) * H) →
      ∀ (d : ℤ × ℤ), IsTraceUnresolved d K H η →
      ∃! Γ : Set TracePlane,
        (∃ x ∈ traceUncutBoundary H,
          connectedComponentIn (traceUncutBoundary H) x = Γ) ∧
        NormedSpace.normalize (euclideanIntDirection d) ∈
          closedAngularNeighborhood (normalsOn traceBasis Γ) η ∧
        ∃ (k : Fin 8) (u v : ℤ × ℤ),
          ConsecutiveCutoffSlopes ⌊H⌋₊ u v ∧
          Γ = slopeBoundaryArc (signedSectorBasis traceBasis k)
            (cutoffSlope u) (cutoffSlope v) ∧
          H ≤ Ch * intEuclidean d *
            (min (intHeight (inverseSignedSectorCoordinates k u))
              (intHeight (inverseSignedSectorCoordinates k v))) ^ 2 ∧
          (signedTraceCutoffArcLength k u v).toReal ≤
            Ca * Real.sqrt (intEuclidean d) / (H * Real.sqrt H) := by
  obtain ⟨Ch, Ca, hCh, hCa, hsize⟩ := trace_unresolved_actual_component_sizes
  refine ⟨Ch, Ca, hCh, hCa, ?_⟩
  intro K H ε η hH hε hη hbasic d hUnresolved
  obtain ⟨Γ, hΓ, hunique⟩ :=
    hUnresolved.unique_component ε hH hε hη hbasic
  obtain ⟨x, hx, hxΓ⟩ := hΓ.1
  have hmem : NormedSpace.normalize (euclideanIntDirection d) ∈
      closedAngularNeighborhood
        (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary H) x)) η := by
    rw [hxΓ]
    exact hΓ.2
  obtain ⟨k, u, v, h, hcomp, hheight, harc⟩ :=
    hsize H ε η hH hε hbasic d hUnresolved.1 x hx hmem
  refine ⟨Γ, ⟨hΓ.1, hΓ.2, k, u, v, h, hxΓ.symm.trans hcomp, hheight, harc⟩, ?_⟩
  intro Δ hΔ
  exact hunique Δ ⟨hΔ.1, hΔ.2.1⟩

end Markov
