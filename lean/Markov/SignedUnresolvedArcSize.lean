import Markov.SignedCutoffHeight
import Markov.GlobalArcLength
import Markov.UnresolvedSizes

/-! The actual Euclidean variation of a signed cutoff component satisfies
the unresolved square-root size estimate. Endpoint arithmetic, the full
normal diameter, and the curve-length scale are supplied by the constructed
trace plane; only membership in the actual angular neighborhood and its
displayed error bound remain conditional. -/

noncomputable section
namespace Markov

/-- Both original endpoints of an actual signed cutoff gap have integral
height at least one, so the smaller endpoint can be used in the size bound. -/
theorem one_le_signedCutoff_min_endpoint_height
    (n : ℕ) (k : Fin 8) (u v : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v) :
    1 ≤ min (intHeight (inverseSignedSectorCoordinates k u))
      (intHeight (inverseSignedSectorCoordinates k v)) := by
  obtain ⟨hu, _, hv, _⟩ := signedConsecutiveCutoffSlopes_height_bounds k n u v h
  exact le_min hu hv

/-- A height estimate at the smaller actual endpoint gives the
square-root bound for the actual Euclidean arc variation. -/
theorem signed_cutoff_arc_sqrt_bound_of_height
    (n : ℕ) (hn : 1 ≤ n) (k : Fin 8) (u v d : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes n u v) (K : ℝ) (hK : 0 ≤ K)
    (hheight : (n : ℝ) ≤ K * intEuclidean d *
      (min (intHeight (inverseSignedSectorCoordinates k u))
        (intHeight (inverseSignedSectorCoordinates k v))) ^ 2) :
    (signedTraceCutoffArcLength k u v).toReal ≤
      traceGlobalCutoffArcLengthConstant * Real.sqrt K * Real.sqrt (intEuclidean d) /
        ((n : ℝ) * Real.sqrt (n : ℝ)) := by
  let A := min (intHeight (inverseSignedSectorCoordinates k u))
    (intHeight (inverseSignedSectorCoordinates k v))
  have hA : 1 ≤ A := one_le_signedCutoff_min_endpoint_height n k u v h
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlength : (signedTraceCutoffArcLength k u v).toReal ≤
      traceGlobalCutoffArcLengthConstant / ((n : ℝ) * A) := by
    have hbase := signedTraceCutoffArcLength_toReal_le_original_heights k n u v h
    change (signedTraceCutoffArcLength k u v).toReal ≤
      2 * (signedTraceEuclideanArcConstant : ℝ) / ((n : ℝ) * A) at hbase
    apply hbase.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    dsimp [traceGlobalCutoffArcLengthConstant]
    linarith
  exact cap_arc_sqrt_bound (signedTraceCutoffArcLength k u v).toReal
    traceGlobalCutoffArcLengthConstant (n : ℝ) A K (intEuclidean d)
    ENNReal.toReal_nonneg traceGlobalCutoffArcLengthConstant_pos.le hnR
    (by linarith) hK (intEuclidean_nonneg d) hlength hheight

/-- Coupled height and actual variation bounds for a signed gap at a
chosen positive decay rate. The explicit diameter argument permits a
common rate shared with a separate corner estimate. -/
theorem signed_cutoff_unresolved_height_and_arc_bound_of_diameter
    (n : ℕ) (hn : 1 ≤ n) (k : Fin 8) (u v d : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes n u v) (hd : d ≠ (0, 0))
    (M N c η : ℝ) (hc : 0 < c)
    (hdiam : Metric.diam (normalsOn traceBasis
      (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))) ≤
        M * Real.exp (-c * (n : ℝ)))
    (hmem : NormedSpace.normalize (euclideanIntDirection d) ∈
      closedAngularNeighborhood (normalsOn traceBasis
        (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))) η)
    (hη : η ≤ N * Real.exp (-c * (n : ℝ))) :
    0 < (traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c ∧
      (n : ℝ) ≤
        ((traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c) *
          intEuclidean d *
            (min (intHeight (inverseSignedSectorCoordinates k u))
              (intHeight (inverseSignedSectorCoordinates k v))) ^ 2 ∧
      (signedTraceCutoffArcLength k u v).toReal ≤
        traceGlobalCutoffArcLengthConstant *
          Real.sqrt ((traceSeparationConstant +
            Real.log (traceNormalArcDetConstant M N) + 1) / c) *
          Real.sqrt (intEuclidean d) / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
  have hheight := signed_cutoff_closedAngularNeighborhood_height_of_diameter
    n k u v d h
    (min (intHeight (inverseSignedSectorCoordinates k u))
      (intHeight (inverseSignedSectorCoordinates k v))) M N c η
    (one_le_signedCutoff_min_endpoint_height n k u v h) le_rfl hd hc hdiam hmem hη
  exact ⟨hheight.1, hheight.2,
    signed_cutoff_arc_sqrt_bound_of_height n hn k u v d h _ hheight.1.le hheight.2⟩

/-- Every signed actual cutoff component has the coupled unresolved
height and square-root variation bounds at uniform positive constants.
All geometric estimates are proved; only the displayed angular membership
and exponential error condition remain hypotheses. -/
theorem signed_cutoff_unresolved_height_and_arc_bound :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (k : Fin 8) (u v d : ℤ × ℤ), ConsecutiveCutoffSlopes n u v → d ≠ (0, 0) →
      ∀ N η : ℝ,
      NormedSpace.normalize (euclideanIntDirection d) ∈
        closedAngularNeighborhood (normalsOn traceBasis
          (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))) η →
      η ≤ N * Real.exp (-c * (n : ℝ)) →
      0 < (traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c ∧
        (n : ℝ) ≤
          ((traceSeparationConstant + Real.log (traceNormalArcDetConstant M N) + 1) / c) *
            intEuclidean d *
              (min (intHeight (inverseSignedSectorCoordinates k u))
                (intHeight (inverseSignedSectorCoordinates k v))) ^ 2 ∧
        (signedTraceCutoffArcLength k u v).toReal ≤
          traceGlobalCutoffArcLengthConstant *
            Real.sqrt ((traceSeparationConstant +
              Real.log (traceNormalArcDetConstant M N) + 1) / c) *
            Real.sqrt (intEuclidean d) / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
  obtain ⟨M, c, hM, hc, hdiam⟩ := signed_cutoff_normal_diam_decay
  refine ⟨M, c, hM, hc, ?_⟩
  intro n hn k u v d h hd N η hmem hη
  exact signed_cutoff_unresolved_height_and_arc_bound_of_diameter n hn k u v d h hd
    M N c η hc (hdiam n hn k u v h) hmem hη

end Markov
