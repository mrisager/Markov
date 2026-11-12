import Markov.TraceChordTurn
import Markov.BoundaryArc

/-! An actual four-chord path on the unit boundary of the trace norm.
Each piece normalizes a chord of the original norm. Its measurability and
boundary membership suffice to transport measures to this actual boundary;
no identification with the full geometric turn measure is asserted here. -/

noncomputable section
open Set

namespace Markov

/-- The measurable structure from the actual trace norm topology. -/
instance tracePlaneMeasurableSpace : MeasurableSpace TracePlane := borel TracePlane

instance tracePlaneBorelSpace : BorelSpace TracePlane := ⟨rfl⟩

/-- The four positively oriented normalized chords, with quarter seams
assigned to the piece on their right. -/
def traceBoundaryPath (t : ℝ) : TracePlane :=
  if t < 1 then radialBasisSection (chordBasis (traceRotationBasis 0)) t
  else if t < 2 then radialBasisSection (chordBasis (traceRotationBasis 1)) (t - 1)
  else if t < 3 then radialBasisSection (chordBasis (traceRotationBasis 2)) (t - 2)
  else radialBasisSection (chordBasis (traceRotationBasis 3)) (t - 3)

theorem traceBoundaryPath_of_lt_one (t : ℝ) (ht : t < 1) :
    traceBoundaryPath t = radialBasisSection (chordBasis (traceRotationBasis 0)) t := by
  simp only [traceBoundaryPath, if_pos ht]

theorem traceBoundaryPath_of_one_le_of_lt_two (t : ℝ) (h1 : 1 ≤ t) (h2 : t < 2) :
    traceBoundaryPath t = radialBasisSection (chordBasis (traceRotationBasis 1)) (t - 1) := by
  simp only [traceBoundaryPath, if_neg (not_lt.mpr h1), if_pos h2]

theorem traceBoundaryPath_of_two_le_of_lt_three (t : ℝ) (h2 : 2 ≤ t) (h3 : t < 3) :
    traceBoundaryPath t = radialBasisSection (chordBasis (traceRotationBasis 2)) (t - 2) := by
  have h1 : 1 ≤ t := by linarith
  simp only [traceBoundaryPath, if_neg (not_lt.mpr h1), if_neg (not_lt.mpr h2), if_pos h3]

theorem traceBoundaryPath_of_three_le (t : ℝ) (h3 : 3 ≤ t) :
    traceBoundaryPath t = radialBasisSection (chordBasis (traceRotationBasis 3)) (t - 3) := by
  have h1 : 1 ≤ t := by linarith
  have h2 : 2 ≤ t := by linarith
  simp only [traceBoundaryPath, if_neg (not_lt.mpr h1), if_neg (not_lt.mpr h2),
    if_neg (not_lt.mpr h3)]

/-- Every point of the path has unit norm in the original trace norm,
including its arbitrary real-parameter extensions. -/
@[simp] theorem norm_traceBoundaryPath (t : ℝ) : ‖traceBoundaryPath t‖ = 1 := by
  unfold traceBoundaryPath
  split_ifs <;> exact norm_radialBasisSection _ _

theorem traceBoundaryPath_mem_frontier (t : ℝ) :
    traceBoundaryPath t ∈ frontier (Metric.closedBall (0 : TracePlane) 1) := by
  rw [frontier_closedBall (0 : TracePlane) (by norm_num : (1 : ℝ) ≠ 0)]
  simpa only [Metric.mem_sphere, dist_zero_right] using norm_traceBoundaryPath t

/-- Each chord piece is continuous, and the three branch tests are Borel
sets, so the actual trace-boundary path is measurable. -/
theorem measurable_traceBoundaryPath : Measurable traceBoundaryPath := by
  have h0 : Measurable (fun t : ℝ =>
      radialBasisSection (chordBasis (traceRotationBasis 0)) t) :=
    (radialBasisSection_continuous _).measurable
  have h1 : Measurable (fun t : ℝ =>
      radialBasisSection (chordBasis (traceRotationBasis 1)) (t - 1)) :=
    (radialBasisSection_continuous _).measurable.comp (measurable_id.sub measurable_const)
  have h2 : Measurable (fun t : ℝ =>
      radialBasisSection (chordBasis (traceRotationBasis 2)) (t - 2)) :=
    (radialBasisSection_continuous _).measurable.comp (measurable_id.sub measurable_const)
  have h3 : Measurable (fun t : ℝ =>
      radialBasisSection (chordBasis (traceRotationBasis 3)) (t - 3)) :=
    (radialBasisSection_continuous _).measurable.comp (measurable_id.sub measurable_const)
  exact Measurable.ite measurableSet_Iio h0
    (Measurable.ite measurableSet_Iio h1 (Measurable.ite measurableSet_Iio h2 h3))

/-- One full traversal returns to its initial actual boundary point. -/
theorem traceBoundaryPath_four_eq_zero : traceBoundaryPath 4 = traceBoundaryPath 0 := by
  rw [traceBoundaryPath_of_three_le 4 (by norm_num),
    traceBoundaryPath_of_lt_one 0 (by norm_num)]
  norm_num [radialBasisSection, chordBasis_zero, chordBasis_one, traceRotationBasis,
    Function.iterate_succ_apply]

end Markov
