import Markov.TraceCompatibility
import Markov.GlobalSeparation
import Markov.UnresolvedSeparation

/-! Uniform arithmetic separation for the constructed trace norm. The
matrix trace compatibility is proved, so the remaining unresolved-height
and arc estimates retain only their explicit determinant upper and arc
comparison hypotheses. -/

noncomputable section
namespace Markov

/-- The uniform separation constant of the constructed trace norm. -/
def traceSeparationConstant : ℝ := planeSeparationConstant traceBasis

theorem traceSeparationConstant_eq :
    traceSeparationConstant = 96 * traceAxisLength + 25 := by
  unfold traceSeparationConstant planeSeparationConstant
  rw [norm_traceBasis_zero, norm_traceBasis_one]
  ring

theorem traceSeparationConstant_pos : 0 < traceSeparationConstant :=
  planeSeparationConstant_pos traceBasis

/-- Separation for every positively oriented integral unimodular pair in
the constructed trace plane. -/
theorem trace_selectedSupport_global_lower_bound_pos
    (u v d : ℤ × ℤ) (A : ℝ) (hA : 1 ≤ A) (hu : intHeight u ≤ A)
    (hdet : intDet u v = 1) (hd : d ≠ (0, 0)) :
    Real.exp (-(traceSeparationConstant * intEuclidean d * A ^ 2)) ≤
      |integralCovectorDet (dualCoordinates traceBasis (selectedSupportAt traceBasis u v)) d| :=
  selectedSupport_global_lower_bound_pos traceBasis tracePlane_quadrantTraceLengthCompatible
    u v d A hA hu hdet hd

/-- Separation for every negatively oriented integral unimodular pair. -/
theorem trace_selectedSupport_global_lower_bound_neg
    (u v d : ℤ × ℤ) (A : ℝ) (hA : 1 ≤ A) (hu : intHeight u ≤ A)
    (hdet : intDet u v = -1) (hd : d ≠ (0, 0)) :
    Real.exp (-(traceSeparationConstant * intEuclidean d * A ^ 2)) ≤
      |integralCovectorDet (dualCoordinates traceBasis (selectedSupportAt traceBasis u v)) d| :=
  selectedSupport_global_lower_bound_neg traceBasis tracePlane_quadrantTraceLengthCompatible
    u v d A hA hu hdet hd

/-- Uniform arithmetic separation in every nonzero integral direction,
with no norm--trace compatibility hypothesis. -/
theorem trace_selectedSupport_global_lower_bound
    (u v d : ℤ × ℤ) (A : ℝ) (hA : 1 ≤ A) (hu : intHeight u ≤ A)
    (hdet : |intDet u v| = 1) (hd : d ≠ (0, 0)) :
    Real.exp (-(traceSeparationConstant * intEuclidean d * A ^ 2)) ≤
      |integralCovectorDet (dualCoordinates traceBasis (selectedSupportAt traceBasis u v)) d| :=
  selectedSupport_global_lower_bound traceBasis tracePlane_quadrantTraceLengthCompatible
    u v d A hA hu hdet hd

/-- A selected support of the constructed trace norm has nonzero
determinant against every nonzero integral direction. -/
theorem trace_selectedSupport_global_det_ne_zero
    (u v d : ℤ × ℤ) (hdet : |intDet u v| = 1) (hd : d ≠ (0, 0)) :
    integralCovectorDet (dualCoordinates traceBasis (selectedSupportAt traceBasis u v)) d ≠ 0 :=
  selectedSupport_global_det_ne_zero traceBasis tracePlane_quadrantTraceLengthCompatible
    u v d hdet hd

/-- Endpoint-height control for the constructed trace norm, conditional
only on the displayed determinant upper estimate. -/
theorem trace_unresolved_direction_height
    (u v d : ℤ × ℤ) (A L c H : ℝ)
    (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hdet : |intDet u v| = 1)
    (hd : d ≠ (0, 0)) (hL : 1 ≤ L) (hc : 0 < c)
    (hupper : |integralCovectorDet
      (dualCoordinates traceBasis (selectedSupportAt traceBasis u v)) d| ≤
      L * intEuclidean d * Real.exp (-c * H)) :
    0 < (traceSeparationConstant + Real.log L + 1) / c ∧
      H ≤ ((traceSeparationConstant + Real.log L + 1) / c) *
        intEuclidean d * A ^ 2 :=
  unresolved_direction_height traceBasis tracePlane_quadrantTraceLengthCompatible
    u v d A L c H hA hu hdet hd hL hc hupper

/-- The unresolved arc scale for the constructed trace norm, with the
determinant upper estimate and the arc comparison left explicit. -/
theorem trace_unresolved_direction_arc_bound
    (u v d : ℤ × ℤ) (A L c H C s : ℝ)
    (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hdet : |intDet u v| = 1)
    (hd : d ≠ (0, 0)) (hL : 1 ≤ L) (hc : 0 < c)
    (hH : 0 < H) (hC : 0 ≤ C) (hs0 : 0 ≤ s)
    (hupper : |integralCovectorDet
      (dualCoordinates traceBasis (selectedSupportAt traceBasis u v)) d| ≤
      L * intEuclidean d * Real.exp (-c * H)) (hs : s ≤ C / (H * A)) :
    s ≤ C * Real.sqrt ((traceSeparationConstant + Real.log L + 1) / c) *
      Real.sqrt (intEuclidean d) / (H * Real.sqrt H) :=
  unresolved_direction_arc_bound traceBasis tracePlane_quadrantTraceLengthCompatible
    u v d A L c H C s hA hu hdet hd hL hc hH hC hs0 hupper hs

end Markov
