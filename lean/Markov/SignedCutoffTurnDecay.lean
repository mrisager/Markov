import Markov.TraceRationalArcDecay
import Markov.TracePositiveConeArc
import Markov.SlopeArcPositiveCone
import Markov.CutoffGapHeightBounds
import Markov.SignedTraceArcs

/-! Actual cutoff components in all eight signed sectors have small total
turn. The whole component is contained in the rational quadrant arc with
its correctly oriented inward supports, including reflected sectors. -/

noncomputable section
open Set MeasureTheory
namespace Markov

/-- Inverse signed coordinates change the basis, not the real vector. -/
theorem signedSectorBasis_intVector_inverse (k : Fin 8) (u : ℤ × ℤ) :
    intVector (signedSectorBasis traceBasis k) u =
      intVector traceBasis (inverseSignedSectorCoordinates k u) := by
  simpa only [coordinates_inverseSignedSectorCoordinates] using
    signedSectorBasis_intVector traceBasis k (inverseSignedSectorCoordinates k u)

/-- Uniform exponential height decay for the actual complete turn mass of
every signed cutoff component. No angular, trace, or tail hypothesis remains. -/
theorem signed_cutoff_arc_turn_height_decay :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (H : ℕ) (k : Fin 8) (u v : ℤ × ℤ),
      ConsecutiveCutoffSlopes H u v →
      (traceBoundaryTurn
        (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))).toReal ≤
        C * (intHeight u + intHeight v) *
          Real.exp (-(c * (intHeight u + intHeight v))) := by
  obtain ⟨C, c, hC, hc, hdecay⟩ := trace_rational_arc_turn_height_decay
  refine ⟨C, c, hC, hc, ?_⟩
  intro H k u v h
  obtain ⟨_, hu0, hu1, _, _⟩ := (mem_cutoffSlopesUpTo H u).mp h.1
  obtain ⟨_, hv0, hv1, _, _⟩ := (mem_cutoffSlopesUpTo H v).mp h.2.1
  have hd := (consecutiveCutoffSlopes_det_and_denominator_sum H u v h).1
  obtain ⟨_, _, _, _, _, _, _, _, hheight, _⟩ :=
    signedConsecutiveCutoffSlopes_height_bounds k H u v h
  obtain ⟨q, M, N, _, _, _, _, _, _, hforward | hreverse⟩ :=
    signedSector_exists_quadrantSeededFarey k u v hu0 hu1 hv0 hv1 hd
  · have hsub : slopeBoundaryArc (signedSectorBasis traceBasis k)
        (cutoffSlope u) (cutoffSlope v) ⊆
        traceBoundaryOpenArc (traceRationalParameter q (inverseSignedSectorCoordinates k u))
          (traceRationalParameter q (inverseSignedSectorCoordinates k v)) := by
      intro x hx
      obtain ⟨α, β, hα, hβ, he⟩ :=
        consecutiveCutoffSlopes_mem_arc_exists_pos_intVector_combination
          (signedSectorBasis traceBasis k) H u v h x hx
      rw [signedSectorBasis_intVector_inverse, signedSectorBasis_intVector_inverse] at he
      rw [← he]
      exact hforward.2.normalize_positiveCombination_mem_traceBoundaryOpenArc α β hα hβ
    have hm := ENNReal.toReal_mono (measure_ne_top traceBoundaryTurn _)
      (measure_mono hsub)
    have hb := hdecay q _ _ M N hforward.2 hheight
    simpa only [inverseSignedSectorCoordinates_height] using hm.trans hb
  · have hsub : slopeBoundaryArc (signedSectorBasis traceBasis k)
        (cutoffSlope u) (cutoffSlope v) ⊆
        traceBoundaryOpenArc (traceRationalParameter q (inverseSignedSectorCoordinates k v))
          (traceRationalParameter q (inverseSignedSectorCoordinates k u)) := by
      intro x hx
      obtain ⟨α, β, hα, hβ, he⟩ :=
        consecutiveCutoffSlopes_mem_arc_exists_pos_intVector_combination
          (signedSectorBasis traceBasis k) H u v h x hx
      rw [signedSectorBasis_intVector_inverse, signedSectorBasis_intVector_inverse] at he
      rw [← he]
      simpa only [add_comm] using
        hreverse.2.normalize_positiveCombination_mem_traceBoundaryOpenArc β α hβ hα
    have hm := ENNReal.toReal_mono (measure_ne_top traceBoundaryTurn _)
      (measure_mono hsub)
    have hheight' : 1 < intHeight
        (inverseSignedSectorCoordinates k v + inverseSignedSectorCoordinates k u) := by
      simpa only [add_comm] using hheight
    have hb := hdecay q _ _ M N hreverse.2 hheight'
    simpa only [inverseSignedSectorCoordinates_height, add_comm] using hm.trans hb

/-- Each actual cutoff component has a uniform `H exp(-c H)` turn bound.
The factor two absorbs the possible endpoint-height sum up to `2H`. -/
theorem signed_cutoff_arc_turn_cutoff_decay :
    ∃ D c : ℝ, 0 < D ∧ 0 < c ∧ ∀ (H : ℕ) (k : Fin 8) (u v : ℤ × ℤ),
      ConsecutiveCutoffSlopes H u v →
      (traceBoundaryTurn
        (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))).toReal ≤
        D * (H : ℝ) * Real.exp (-(c * (H : ℝ))) := by
  obtain ⟨C, c, hC, hc, hdecay⟩ := signed_cutoff_arc_turn_height_decay
  refine ⟨2 * C, c, mul_pos (by norm_num) hC, hc, ?_⟩
  intro H k u v h
  obtain ⟨_, _, _, _, _, _, hsumH, hsum2H, _, _⟩ :=
    signedConsecutiveCutoffSlopes_height_bounds k H u v h
  simp only [inverseSignedSectorCoordinates_height] at hsumH hsum2H
  apply (hdecay H k u v h).trans
  have he : Real.exp (-(c * (intHeight u + intHeight v))) ≤
      Real.exp (-(c * (H : ℝ))) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hsumH.le hc.le))
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hsum2H hC.le) he
    (Real.exp_pos _).le (mul_nonneg hC.le (by positivity : (0 : ℝ) ≤ 2 * H))
  convert hh using 1
  ring

end Markov
