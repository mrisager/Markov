import Markov.TraceRationalParameters
import Markov.ChordRationalSupport

/-! The actual inward selected supports at integral quadrant rays coincide
with the outgoing and incoming selectors in the rational chord chart.
Only coordinates change; no symmetry of the norm is assumed. -/

noncomputable section
namespace Markov

/-- Quarter coordinates represent the identical two real vectors, hence
the identical selected support in the original trace norm. -/
theorem selectedSupportAt_traceRotation_coordinates (k : Fin 4) (u v : ℤ × ℤ)
    (hd : intDet u v ≠ 0) :
    selectedSupportAt traceBasis u v =
      selectedSupportAt (traceRotationBasis k.val)
        (quadrantCoordinates k u) (quadrantCoordinates k v) := by
  have hdc : intDet (quadrantCoordinates k u) (quadrantCoordinates k v) ≠ 0 := by
    rwa [quadrantCoordinates_det]
  have hu : intVector (traceRotationBasis k.val) (quadrantCoordinates k u) =
      intVector traceBasis u := traceRotationBasis_quadrantCoordinates k u
  have hv : intVector (traceRotationBasis k.val) (quadrantCoordinates k v) =
      intVector traceBasis v := traceRotationBasis_quadrantCoordinates k v
  have hs := selectedSupportAt_spec (traceRotationBasis k.val)
    (quadrantCoordinates k u) (quadrantCoordinates k v) hdc
  rw [hu, hv] at hs
  apply (exists_unique_selectedSupport (intPairBasis traceBasis u v hd)).unique
  · simpa only [intPairBasis_zero, intPairBasis_one] using
      selectedSupportAt_spec traceBasis u v hd
  · simpa only [intPairBasis_zero, intPairBasis_one] using hs

/-- The two actual integral selectors are exactly the inward chord
selectors at their actual rational boundary parameters. -/
theorem SeededFarey.trace_rational_inward_supports (k : Fin 4)
    {u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      M0 N0 u v M N) :
    selectedSupportAt traceBasis u v =
        chordSelectedSupport (traceRotationBasis k.val) (traceRationalQuarterParameter k u) ∧
      selectedSupportAt traceBasis v u =
        chordLeftSelectedSupport (traceRotationBasis k.val) (traceRationalQuarterParameter k v) := by
  have hd : intDet u v = 1 := h.det_eq_seed.trans (quadrantSeed_det_eq_one k)
  have hdc : intDet (quadrantCoordinates k u) (quadrantCoordinates k v) = 1 := by
    rw [quadrantCoordinates_det, hd]
  have hd0 : intDet u v ≠ 0 := by simp [hd]
  have hdr : intDet v u ≠ 0 := by
    simp only [intDet] at *
    intro hz
    nlinarith
  constructor
  · rw [selectedSupportAt_traceRotation_coordinates k u v hd0]
    exact selectedSupportAt_eq_chordSelectedSupport (traceRotationBasis k.val)
      (quadrantCoordinates k u) (quadrantCoordinates k v)
      (profileMass_pos _ h.quadrant_left_nonnegativePrimitive) hdc
  · rw [selectedSupportAt_traceRotation_coordinates k v u hdr]
    exact selectedSupportAt_rev_eq_chordLeftSelectedSupport (traceRotationBasis k.val)
      (quadrantCoordinates k u) (quadrantCoordinates k v)
      (profileMass_pos _ h.quadrant_right_nonnegativePrimitive) hdc

end Markov
