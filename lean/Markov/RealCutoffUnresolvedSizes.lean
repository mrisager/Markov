import Markov.SignedUnresolvedArcSize
import Markov.CutoffParameterBounds
import Markov.TraceCornerEstimate

/-! The real-cutoff height and square-root variation estimates for every
actual signed component associated to an unresolved direction. The paper's
basic angular-error assumption supplies the error bound at a common positive
rate. No exponential-error hypothesis remains in the conclusion. This is a
theorem for the constructed trace ball, not its geometric identification. -/

noncomputable section
namespace Markov

/-- The height coefficient at a chosen diameter constant and common rate. -/
def traceUnresolvedHeightCoefficient (M c : ℝ) : ℝ :=
  (traceSeparationConstant +
    Real.log (traceNormalArcDetConstant M (traceCornerLowerConstant / 2)) + 1) / c

theorem traceUnresolvedHeightCoefficient_pos (M c : ℝ) (hc : 0 < c) :
    0 < traceUnresolvedHeightCoefficient M c := by
  have hlog := Real.log_nonneg
    (one_le_traceNormalArcDetConstant M (traceCornerLowerConstant / 2))
  exact div_pos (by linarith [traceSeparationConstant_pos]) hc

/-- Lemma 6's two quantitative conclusions for all signed actual cutoff
components, at a real cutoff. The constants are independent of the cutoff,
direction, sector and error radius. The tested direction and the smaller
endpoint height are both in the original coordinates. -/
theorem real_cutoff_signed_unresolved_height_and_arc_bound :
    ∃ Ch Ca : ℝ, 0 < Ch ∧ 0 < Ca ∧
      ∀ (H ε η : ℝ), 1 ≤ H → 0 < ε →
      (2 + ε) * η ≤ traceCornerLowerConstant *
        Real.exp (-(2 * traceAxisLength) * H) →
      ∀ (k : Fin 8) (u v d : ℤ × ℤ),
      ConsecutiveCutoffSlopes ⌊H⌋₊ u v → d ≠ (0, 0) →
      NormedSpace.normalize (euclideanIntDirection d) ∈
        closedAngularNeighborhood (normalsOn traceBasis
          (slopeBoundaryArc (signedSectorBasis traceBasis k)
            (cutoffSlope u) (cutoffSlope v))) η →
      H ≤ Ch * intEuclidean d *
        (min (intHeight (inverseSignedSectorCoordinates k u))
          (intHeight (inverseSignedSectorCoordinates k v))) ^ 2 ∧
      (signedTraceCutoffArcLength k u v).toReal ≤
        Ca * Real.sqrt (intEuclidean d) / (H * Real.sqrt H) := by
  obtain ⟨M, cD, hM, hcD, hdiam⟩ := signed_cutoff_normal_diam_decay
  have haxis := traceAxisLength_pos
  have harcC := traceGlobalCutoffArcLengthConstant_pos
  let c := min cD (2 * traceAxisLength)
  have hc : 0 < c := lt_min hcD (by positivity)
  let L := traceUnresolvedHeightCoefficient M c
  have hL : 0 < L := traceUnresolvedHeightCoefficient_pos M c hc
  refine ⟨2 * L, 4 * (traceGlobalCutoffArcLengthConstant * Real.sqrt L),
    by positivity, by positivity, ?_⟩
  intro H ε η hH hε hbasic k u v d h hd hmem
  have hd0 := intEuclidean_nonneg d
  have hn : 1 ≤ ⌊H⌋₊ := (cutoff_natFloor_bounds H hH).1
  have hdiam' : Metric.diam (normalsOn traceBasis
      (slopeBoundaryArc (signedSectorBasis traceBasis k)
        (cutoffSlope u) (cutoffSlope v))) ≤
      M * Real.exp (-c * (⌊H⌋₊ : ℝ)) := by
    apply (hdiam ⌊H⌋₊ hn k u v h).trans
    apply mul_le_mul_of_nonneg_left _ hM.le
    apply Real.exp_le_exp.mpr
    have hrate : c ≤ cD := min_le_left _ _
    have := mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg ⌊H⌋₊ : (0 : ℝ) ≤ _)
    linarith
  have hη : η ≤ (traceCornerLowerConstant / 2) *
      Real.exp (-c * (⌊H⌋₊ : ℝ)) :=
    cutoff_eta_le_common_rate_natFloor_of_basic_assumption
      traceCornerLowerConstant ε cD (2 * traceAxisLength) H η
      traceCornerLowerConstant_pos hε hcD (by positivity) hH hbasic
  obtain ⟨_, hheight, harc⟩ :=
    signed_cutoff_unresolved_height_and_arc_bound_of_diameter
      ⌊H⌋₊ hn k u v d h hd M (traceCornerLowerConstant / 2) c η
      hc hdiam' hmem hη
  change (⌊H⌋₊ : ℝ) ≤ L * intEuclidean d *
    (min (intHeight (inverseSignedSectorCoordinates k u))
      (intHeight (inverseSignedSectorCoordinates k v))) ^ 2 at hheight
  change (signedTraceCutoffArcLength k u v).toReal ≤
    traceGlobalCutoffArcLengthConstant * Real.sqrt L * Real.sqrt (intEuclidean d) /
      ((⌊H⌋₊ : ℝ) * Real.sqrt (⌊H⌋₊ : ℝ)) at harc
  refine ⟨cutoff_real_height_le_of_natFloor_le H L (intEuclidean d) _ hH hheight, ?_⟩
  have hreal := cutoff_arc_bound_of_natFloor_bound H
    (traceGlobalCutoffArcLengthConstant * Real.sqrt L * Real.sqrt (intEuclidean d))
    (signedTraceCutoffArcLength k u v).toReal hH (by positivity) harc
  convert hreal using 1
  ring

end Markov
