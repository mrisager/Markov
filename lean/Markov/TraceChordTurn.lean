import Markov.ChordCharts
import Markov.TraceLocalTurn

/-! Four actual positively oriented chord charts of the trace norm.
Each angle is obtained from its actual selected support and extended
constantly outside the closed unit parameter interval. These are actual
local Stieltjes lifts for the four full quadrants, before cyclic gluing. -/

noncomputable section
open Set
open scoped Topology
namespace Markov

def traceRotationBasis (i : ℕ) : Module.Basis (Fin 2) ℝ TracePlane :=
  (quarterTurnBasis^[i]) traceBasis

@[simp] theorem traceRotationBasis_zero : traceRotationBasis 0 = traceBasis := rfl

theorem traceRotationBasis_succ (i : ℕ) :
    traceRotationBasis (i + 1) = quarterTurnBasis (traceRotationBasis i) :=
  Function.iterate_succ_apply' _ _ _

theorem norm_traceRotationBasis_zero (i : Fin 4) :
    ‖traceRotationBasis i.val 0‖ = traceAxisLength := by
  fin_cases i <;> simp [traceRotationBasis, Function.iterate_succ_apply,
    quarterTurnBasis_zero, quarterTurnBasis_one]

theorem norm_traceRotationBasis_one (i : Fin 4) :
    ‖traceRotationBasis i.val 1‖ = traceAxisLength := by
  fin_cases i <;> simp [traceRotationBasis, Function.iterate_succ_apply,
    quarterTurnBasis_zero, quarterTurnBasis_one]

theorem norm_traceRotationBasis_sub_lt (i : Fin 4) :
    ‖traceRotationBasis i.val 0 - traceRotationBasis i.val 1‖ < 2 * traceAxisLength := by
  fin_cases i
  · exact norm_traceBasis_sub_lt_twice_axis
  · simp only [traceRotationBasis, Function.iterate_succ_apply, Function.iterate_zero_apply,
      quarterTurnBasis_zero, quarterTurnBasis_one, sub_neg_eq_add]
    rw [add_comm, norm_traceBasis_sum]
    linarith [traceAxisLength_pos]
  · simp only [traceRotationBasis, Function.iterate_succ_apply, Function.iterate_zero_apply,
      quarterTurnBasis_zero, quarterTurnBasis_one]
    rw [show -traceBasis 0 - -traceBasis 1 = -(traceBasis 0 - traceBasis 1) by module,
      norm_neg]
    exact norm_traceBasis_sub_lt_twice_axis
  · have h : ‖-traceBasis 1 - traceBasis 0‖ = traceAxisLength := by
      rw [show -traceBasis 1 - traceBasis 0 = -(traceBasis 0 + traceBasis 1) by module,
        norm_neg, norm_traceBasis_sum]
    simp only [traceRotationBasis, Function.iterate_succ_apply, Function.iterate_zero_apply,
      quarterTurnBasis_zero, quarterTurnBasis_one, neg_neg]
    rw [h]
    linarith [traceAxisLength_pos]

def traceChordAngle (i : Fin 4) (t : ℝ) : ℝ :=
  chordSelectedAngle (traceRotationBasis i.val) (quarterClamp t)

theorem traceChordAngle_monotone (i : Fin 4) : Monotone (traceChordAngle i) := by
  intro s t hst
  exact (chordSelectedAngle_monotoneOn (traceRotationBasis i.val) traceAxisLength
    (norm_traceRotationBasis_zero i) (norm_traceRotationBasis_one i)
    (norm_traceRotationBasis_sub_lt i)) (quarterClamp_mem s) (quarterClamp_mem t)
    (quarterClamp_monotone hst)

theorem traceChordAngle_continuousWithinAt_right (i : Fin 4) (t : ℝ) :
    ContinuousWithinAt (traceChordAngle i) (Ici t) t := by
  exact (chordSelectedAngle_continuousWithinAt_right (traceRotationBasis i.val)
    traceAxisLength (norm_traceRotationBasis_zero i) (norm_traceRotationBasis_one i)
    (norm_traceRotationBasis_sub_lt i) (quarterClamp t) (quarterClamp_mem t)).comp
      quarterClamp_continuous.continuousWithinAt
      (fun s hs => quarterClamp_monotone hs)

def traceChordAngleLift (i : Fin 4) : StieltjesFunction ℝ where
  toFun := traceChordAngle i
  mono' := traceChordAngle_monotone i
  right_continuous' := traceChordAngle_continuousWithinAt_right i

theorem traceChordAngleLift_eq_chord (i : Fin 4) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    traceChordAngleLift i t = chordSelectedAngle (traceRotationBasis i.val) t := by
  change chordSelectedAngle (traceRotationBasis i.val) (quarterClamp t) = _
  rw [quarterClamp_eq_self t ht]

end Markov
