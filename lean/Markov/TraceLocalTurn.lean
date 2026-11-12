import Markov.AffineSupport
import Markov.HalfPlaneAngleOrder
import Markov.NormalHalfPlane
import Markov.TurnMeasure
import Mathlib.Topology.Order.LeftRight

/-! A genuine local turn measure built from the actual trace norm's
selected support angle. The parameter is clamped to the canonical quarter
section and extended constantly outside it. Global cyclic gluing, geometric
corner identification and quantitative tails are not asserted here. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Markov

def traceSelectedAngle (t : ℝ) : ℝ :=
  supportAngle traceBasis (selectedAffineSupport traceBasis t)

theorem traceSelectedAngle_monotoneOn : MonotoneOn traceSelectedAngle (Icc (0 : ℝ) 1) := by
  apply normingSupport_basisLine_supportAngle_monotoneOn traceBasis _
    (selectedAffineSupport traceBasis)
  · intro t ht
    exact selectedAffineSupport_mem_normingFunctionals traceBasis t
  · intro t ht
    simpa only [map_add] using trace_normingFunctional_sum_pos_Icc t ht
      (selectedAffineSupport traceBasis t)
      (selectedAffineSupport_mem_normingFunctionals traceBasis t)

theorem traceSelectedAngle_continuousWithinAt_right (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousWithinAt traceSelectedAngle (Ici t) t := by
  apply continuousWithinAt_Ioi_iff_Ici.mp
  apply supportAngle_selectedAffineSupport_continuousWithinAt_right
  simpa only [map_add] using trace_normingFunctional_sum_pos_Icc t ht
    (selectedAffineSupport traceBasis t)
    (selectedAffineSupport_mem_normingFunctionals traceBasis t)

def quarterClamp (t : ℝ) : ℝ := max 0 (min 1 t)

theorem quarterClamp_mem (t : ℝ) : quarterClamp t ∈ Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem quarterClamp_monotone : Monotone quarterClamp :=
  monotone_const.max (monotone_const.min monotone_id)

theorem quarterClamp_continuous : Continuous quarterClamp :=
  continuous_const.max (continuous_const.min continuous_id)

theorem quarterClamp_eq_self (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : quarterClamp t = t := by
  rw [quarterClamp, min_eq_right ht.2, max_eq_right ht.1]

def traceQuarterAngle (t : ℝ) : ℝ := traceSelectedAngle (quarterClamp t)

theorem traceQuarterAngle_monotone : Monotone traceQuarterAngle := by
  intro s t hst
  exact traceSelectedAngle_monotoneOn (quarterClamp_mem s) (quarterClamp_mem t)
    (quarterClamp_monotone hst)

theorem traceQuarterAngle_continuousWithinAt_right (t : ℝ) :
    ContinuousWithinAt traceQuarterAngle (Ici t) t := by
  exact (traceSelectedAngle_continuousWithinAt_right (quarterClamp t) (quarterClamp_mem t)).comp
    quarterClamp_continuous.continuousWithinAt
    (fun s hs => quarterClamp_monotone hs)

/-- An actual right-continuous, monotone support-angle lift on this local
section, built from the trace norm rather than supplied as a hypothesis. -/
def traceQuarterAngleLift : StieltjesFunction ℝ where
  toFun := traceQuarterAngle
  mono' := traceQuarterAngle_monotone
  right_continuous' := traceQuarterAngle_continuousWithinAt_right

/-- The genuine Stieltjes measure of the actual local support-angle lift. -/
def traceQuarterTurnMeasure : Measure ℝ := angleTurnMeasure traceQuarterAngleLift

theorem traceQuarterAngleLift_eq_selected (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    traceQuarterAngleLift t = traceSelectedAngle t := by
  change traceSelectedAngle (quarterClamp t) = traceSelectedAngle t
  rw [quarterClamp_eq_self t ht]

theorem traceQuarterTurnMeasure_Ioc (a b : ℝ) :
    traceQuarterTurnMeasure (Ioc a b) =
      ENNReal.ofReal (traceQuarterAngle b - traceQuarterAngle a) :=
  angleTurnMeasure_Ioc traceQuarterAngleLift a b

theorem traceQuarterTurnMeasure_Ioc_selected (a b : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    traceQuarterTurnMeasure (Ioc a b) =
      ENNReal.ofReal (traceSelectedAngle b - traceSelectedAngle a) := by
  rw [traceQuarterTurnMeasure_Ioc]
  simp only [traceQuarterAngle, quarterClamp_eq_self a ha, quarterClamp_eq_self b hb]

theorem traceQuarterTurnMeasure_singleton (t : ℝ) :
    traceQuarterTurnMeasure {t} =
      ENNReal.ofReal (traceQuarterAngle t - Function.leftLim traceQuarterAngle t) :=
  angleTurnMeasure_singleton traceQuarterAngleLift t

theorem traceQuarterTurnMeasure_Ioc_lt_top (a b : ℝ) :
    traceQuarterTurnMeasure (Ioc a b) < ∞ := by
  rw [traceQuarterTurnMeasure_Ioc]
  exact ENNReal.ofReal_lt_top

end Markov
