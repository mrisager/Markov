import Markov.TraceCyclicTurn
import Markov.TraceBoundaryPath

/-! The boundary turn measure is the pushforward of the support-angle
measure through the four-chord boundary path. It has total mass `2 * π`
and is supported on the trace boundary. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Markov

def traceBoundaryTurn : Measure TracePlane :=
  Measure.map traceBoundaryPath traceCyclicParameterTurn

theorem traceBoundaryTurn_apply (S : Set TracePlane) (hS : MeasurableSet S) :
    traceBoundaryTurn S = traceCyclicParameterTurn (traceBoundaryPath ⁻¹' S) := by
  exact Measure.map_apply measurable_traceBoundaryPath hS

theorem traceBoundaryTurn_univ :
    traceBoundaryTurn univ = ENNReal.ofReal (2 * Real.pi) := by
  rw [traceBoundaryTurn_apply univ MeasurableSet.univ, Set.preimage_univ,
    traceCyclicParameterTurn_univ]

instance traceBoundaryTurn_isFiniteMeasure : IsFiniteMeasure traceBoundaryTurn where
  measure_univ_lt_top := by
    rw [traceBoundaryTurn_univ]
    exact ENNReal.ofReal_lt_top

theorem traceBoundaryTurn_frontier :
    traceBoundaryTurn (frontier (Metric.closedBall (0 : TracePlane) 1)) =
      ENNReal.ofReal (2 * Real.pi) := by
  rw [traceBoundaryTurn_apply _ isClosed_frontier.measurableSet]
  have hpre : traceBoundaryPath ⁻¹' frontier (Metric.closedBall (0 : TracePlane) 1) = univ := by
    ext t
    exact iff_true_intro (traceBoundaryPath_mem_frontier t)
  rw [hpre, traceCyclicParameterTurn_univ]

theorem traceBoundaryTurn_compl_frontier :
    traceBoundaryTurn (frontier (Metric.closedBall (0 : TracePlane) 1))ᶜ = 0 := by
  rw [traceBoundaryTurn_apply _ isClosed_frontier.measurableSet.compl]
  have hpre : traceBoundaryPath ⁻¹' (frontier (Metric.closedBall (0 : TracePlane) 1))ᶜ = ∅ := by
    ext t
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false]
    exact not_not_intro (traceBoundaryPath_mem_frontier t)
  rw [hpre, measure_empty]

/-- Boundary-set masses are computed by their actual parameter preimages.
No unstated interval or singleton preimage identity is used. -/
theorem traceBoundaryTurn_apply_eq_parameter_turn (S : Set TracePlane)
    (hS : MeasurableSet S) :
    traceBoundaryTurn S = angleTurnMeasure traceCyclicAngleLift
      (traceBoundaryPath ⁻¹' S ∩ Ioc (0 : ℝ) 4) := by
  rw [traceBoundaryTurn_apply S hS]
  exact Measure.restrict_apply (hS.preimage measurable_traceBoundaryPath)

end Markov
