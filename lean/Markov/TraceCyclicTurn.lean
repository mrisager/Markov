import Markov.TraceChordTurn
import Markov.SupportQuarterRotation
import Markov.StieltjesGlue

/-! The four actual trace support-angle charts, with their proved seam
compatibility, give a single monotone right-continuous lift on one boundary
period. The lift is constant outside [0,4]. Its increment over that period
is exactly 2π. This module does not prove an exponential turn estimate. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Markov

def traceShiftedChordLift (i : Fin 4) : StieltjesFunction ℝ :=
  stieltjesTranslate (traceChordAngleLift i) (i.val : ℝ) ((i.val : ℝ) * Real.pi / 2)

theorem traceShiftedChordLift_apply (i : Fin 4) (t : ℝ) :
    traceShiftedChordLift i t =
      traceChordAngleLift i (t - (i.val : ℝ)) + (i.val : ℝ) * Real.pi / 2 := rfl

theorem traceShiftedChordLift_seam_one :
    traceShiftedChordLift 0 1 = traceShiftedChordLift 1 1 := by
  have h := chordSelectedAngle_seam (traceRotationBasis 0)
  rw [← traceRotationBasis_succ] at h
  simp only [traceShiftedChordLift_apply]
  norm_num only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one,
    sub_zero, sub_self, zero_mul, zero_div, one_mul, add_zero]
  rw [traceChordAngleLift_eq_chord 0 1 (by norm_num),
    traceChordAngleLift_eq_chord 1 0 (by norm_num)]
  exact h

theorem traceShiftedChordLift_seam_two :
    traceShiftedChordLift 1 2 = traceShiftedChordLift 2 2 := by
  have h := chordSelectedAngle_seam (traceRotationBasis 1)
  rw [← traceRotationBasis_succ] at h
  norm_num only [Nat.reduceAdd] at h
  simp only [traceShiftedChordLift_apply]
  norm_num only [Fin.coe_ofNat_eq_mod, Fin.val_one, Nat.reduceMod, Nat.cast_ofNat,
    Nat.cast_one, sub_self, one_mul, show (2 : ℝ) - 1 = 1 by norm_num]
  rw [traceChordAngleLift_eq_chord 1 1 (by norm_num),
    traceChordAngleLift_eq_chord 2 0 (by norm_num)]
  simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod] at *
  linarith only [h]

theorem traceShiftedChordLift_seam_three :
    traceShiftedChordLift 2 3 = traceShiftedChordLift 3 3 := by
  have h := chordSelectedAngle_seam (traceRotationBasis 2)
  rw [← traceRotationBasis_succ] at h
  norm_num only [Nat.reduceAdd] at h
  simp only [traceShiftedChordLift_apply]
  norm_num only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat, sub_self,
    show (3 : ℝ) - 2 = 1 by norm_num]
  rw [traceChordAngleLift_eq_chord 2 1 (by norm_num),
    traceChordAngleLift_eq_chord 3 0 (by norm_num)]
  simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod] at *
  linarith only [h]

def traceFirstTwoChordLift : StieltjesFunction ℝ :=
  stieltjesGlue (traceShiftedChordLift 0) (traceShiftedChordLift 1) 1
    traceShiftedChordLift_seam_one

theorem traceFirstTwoChordLift_seam_two :
    traceFirstTwoChordLift 2 = traceShiftedChordLift 2 2 := by
  rw [traceFirstTwoChordLift, stieltjesGlue_of_ge _ _ _ _ _ (by norm_num)]
  exact traceShiftedChordLift_seam_two

def traceFirstThreeChordLift : StieltjesFunction ℝ :=
  stieltjesGlue traceFirstTwoChordLift (traceShiftedChordLift 2) 2
    traceFirstTwoChordLift_seam_two

theorem traceFirstThreeChordLift_seam_three :
    traceFirstThreeChordLift 3 = traceShiftedChordLift 3 3 := by
  rw [traceFirstThreeChordLift, stieltjesGlue_of_ge _ _ _ _ _ (by norm_num)]
  exact traceShiftedChordLift_seam_three

/-- The actual support-angle lift, assembled from four compatible
quadrant charts in the original trace norm. -/
def traceCyclicAngleLift : StieltjesFunction ℝ :=
  stieltjesGlue traceFirstThreeChordLift (traceShiftedChordLift 3) 3
    traceFirstThreeChordLift_seam_three

theorem traceCyclicAngleLift_of_lt_one (t : ℝ) (ht : t < 1) :
    traceCyclicAngleLift t = traceShiftedChordLift 0 t := by
  simp only [traceCyclicAngleLift, traceFirstThreeChordLift, traceFirstTwoChordLift,
    stieltjesGlue_apply, if_pos ht, if_pos (show t < 2 by linarith),
    if_pos (show t < 3 by linarith)]

theorem traceCyclicAngleLift_of_one_le_of_lt_two (t : ℝ) (h0 : 1 ≤ t) (h1 : t < 2) :
    traceCyclicAngleLift t = traceShiftedChordLift 1 t := by
  simp only [traceCyclicAngleLift, traceFirstThreeChordLift, traceFirstTwoChordLift,
    stieltjesGlue_apply, if_neg (not_lt.mpr h0), if_pos h1,
    if_pos (show t < 3 by linarith)]

theorem traceCyclicAngleLift_of_two_le_of_lt_three (t : ℝ) (h0 : 2 ≤ t) (h1 : t < 3) :
    traceCyclicAngleLift t = traceShiftedChordLift 2 t := by
  simp only [traceCyclicAngleLift, traceFirstThreeChordLift,
    stieltjesGlue_apply, if_neg (not_lt.mpr h0), if_pos h1]

theorem traceCyclicAngleLift_of_three_le (t : ℝ) (ht : 3 ≤ t) :
    traceCyclicAngleLift t = traceShiftedChordLift 3 t := by
  exact stieltjesGlue_of_ge _ _ _ _ _ ht

theorem traceCyclicAngleLift_zero :
    traceCyclicAngleLift 0 = chordSelectedAngle traceBasis 0 := by
  simp only [traceCyclicAngleLift, traceFirstThreeChordLift, traceFirstTwoChordLift,
    stieltjesGlue_apply]
  norm_num only [show (0 : ℝ) < 3 by norm_num, show (0 : ℝ) < 2 by norm_num,
    show (0 : ℝ) < 1 by norm_num, if_true]
  rw [traceShiftedChordLift_apply]
  norm_num only [Fin.val_zero, Nat.cast_zero, sub_zero, zero_mul, zero_div, add_zero]
  rw [traceChordAngleLift_eq_chord 0 0 (by norm_num)]
  rfl

theorem traceCyclicAngleLift_four :
    traceCyclicAngleLift 4 = chordSelectedAngle traceBasis 0 + 2 * Real.pi := by
  have h := chordSelectedAngle_seam (traceRotationBasis 3)
  rw [← traceRotationBasis_succ] at h
  have hfour : traceRotationBasis 4 = traceBasis := quarterTurnBasis_iterate_four traceBasis
  rw [hfour] at h
  rw [traceCyclicAngleLift, stieltjesGlue_of_ge _ _ _ _ _ (by norm_num),
    traceShiftedChordLift_apply]
  norm_num only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat,
    show (4 : ℝ) - 3 = 1 by norm_num]
  rw [traceChordAngleLift_eq_chord 3 1 (by norm_num)]
  simp only [Fin.coe_ofNat_eq_mod, Nat.reduceMod] at *
  linarith only [h]

theorem traceCyclicAngleLift_period_increment :
    traceCyclicAngleLift 4 - traceCyclicAngleLift 0 = 2 * Real.pi := by
  rw [traceCyclicAngleLift_four, traceCyclicAngleLift_zero]
  ring

/-- Turn on one half-open boundary period. The seam at 4 is counted once. -/
def traceCyclicParameterTurn : Measure ℝ := angleTurnMeasureOn traceCyclicAngleLift 0 4

theorem traceCyclicParameterTurn_univ :
    traceCyclicParameterTurn univ = ENNReal.ofReal (2 * Real.pi) := by
  rw [traceCyclicParameterTurn, angleTurnMeasureOn_univ, traceCyclicAngleLift_period_increment]

instance traceCyclicParameterTurn_isFiniteMeasure : IsFiniteMeasure traceCyclicParameterTurn :=
  angleTurnMeasureOn_isFiniteMeasure traceCyclicAngleLift 0 4

end Markov
