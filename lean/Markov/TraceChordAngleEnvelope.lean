import Markov.TraceFullCornerArc
import Markov.TraceChordArcBounds

/-! The complete support-angle envelope of an actual open quarter arc is
bounded by the two inward endpoint angles. Consequently every nonempty
subset of that arc has angular width at most its actual full turn. -/

noncomputable section
open Set

namespace Markov

/-- The full support fibre at an interior chord point lies between the
outgoing initial endpoint angle and the incoming terminal endpoint angle. -/
theorem traceBoundaryPath_chord_supportAngle_mem_Icc
    (k : Fin 4) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (s : ℝ) (hs : s ∈ Ioo a b) (f : StrongDual ℝ TracePlane)
    (hf : f ∈ normingFunctionals (traceBoundaryPath ((k.val : ℝ) + s))) :
    supportAngle (traceRotationBasis k.val) f ∈
      Icc (chordSelectedAngle (traceRotationBasis k.val) a)
        (chordLeftSelectedAngle (traceRotationBasis k.val) b) := by
  have hs0 : 0 < s := lt_of_le_of_lt ha hs.1
  have hs1 : s < 1 := lt_of_lt_of_le hs.2 hb
  have hfangle : supportAngle (traceRotationBasis k.val) f ∈
      Icc (chordLeftSelectedAngle (traceRotationBasis k.val) s)
        (chordSelectedAngle (traceRotationBasis k.val) s) := by
    rw [← traceBoundaryPath_corner_supportAngles_eq_Icc k s ⟨hs0.le, hs1.le⟩]
    exact ⟨f, hf, rfl⟩
  have hlo := traceCyclicAngleLift.mono.le_leftLim
    (show (k.val : ℝ) + a < (k.val : ℝ) + s by linarith [hs.1])
  rw [traceCyclicAngleLift_at_chord k a ⟨ha, by linarith⟩,
    traceCyclicAngleLift_leftLim_at_chord k s ⟨hs0, hs1.le⟩] at hlo
  have hhi := traceCyclicAngleLift.mono.le_leftLim
    (show (k.val : ℝ) + s < (k.val : ℝ) + b by linarith [hs.2])
  rw [traceCyclicAngleLift_at_chord k s ⟨hs0.le, hs1.le⟩,
    traceCyclicAngleLift_leftLim_at_chord k b ⟨by linarith, hb⟩] at hhi
  constructor <;> linarith [hfangle.1, hfangle.2]

/-- All actual support angles over an open quarter arc lie in its inward
endpoint interval, with all interior corner fibres included. -/
theorem supportAnglesOn_traceBoundaryOpenArc_subset_Icc
    (k : Fin 4) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    supportAnglesOn (traceRotationBasis k.val)
        (traceBoundaryOpenArc ((k.val : ℝ) + a) ((k.val : ℝ) + b)) ⊆
      Icc (chordSelectedAngle (traceRotationBasis k.val) a)
        (chordLeftSelectedAngle (traceRotationBasis k.val) b) := by
  rintro θ ⟨x, ⟨t, ht, rfl⟩, f, hf, rfl⟩
  have hs : t - (k.val : ℝ) ∈ Ioo a b :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hf' : f ∈ normingFunctionals
      (traceBoundaryPath ((k.val : ℝ) + (t - (k.val : ℝ)))) := by
    simpa only [add_sub_cancel] using hf
  exact traceBoundaryPath_chord_supportAngle_mem_Icc k a b ha hab hb
    (t - (k.val : ℝ)) hs f hf'

/-- Passing to any nonempty subset preserves the inward endpoint bounds
for the infimum and supremum of all its actual support angles. -/
theorem traceChord_supportAngleLower_upper_bounds
    (k : Fin 4) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (S : Set TracePlane) (hS : S.Nonempty)
    (hsub : S ⊆ traceBoundaryOpenArc ((k.val : ℝ) + a) ((k.val : ℝ) + b)) :
    chordSelectedAngle (traceRotationBasis k.val) a ≤
        supportAngleLower (traceRotationBasis k.val) S ∧
      supportAngleUpper (traceRotationBasis k.val) S ≤
        chordLeftSelectedAngle (traceRotationBasis k.val) b := by
  have hnon := supportAnglesOn_nonempty (traceRotationBasis k.val) S hS
  have hangle : supportAnglesOn (traceRotationBasis k.val) S ⊆
      Icc (chordSelectedAngle (traceRotationBasis k.val) a)
        (chordLeftSelectedAngle (traceRotationBasis k.val) b) := by
    rintro θ ⟨x, hx, f, hf, rfl⟩
    exact supportAnglesOn_traceBoundaryOpenArc_subset_Icc k a b ha hab hb
      ⟨x, hsub hx, f, hf, rfl⟩
  exact ⟨le_csInf hnon (fun θ hθ => (hangle hθ).1),
    csSup_le hnon (fun θ hθ => (hangle hθ).2)⟩

/-- The complete angle envelope of any nonempty subset of an actual open
quarter arc is no wider than that arc's genuine boundary turn. -/
theorem supportAngleWidth_le_traceBoundaryTurn_chord_openArc
    (k : Fin 4) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (S : Set TracePlane) (hS : S.Nonempty)
    (hsub : S ⊆ traceBoundaryOpenArc ((k.val : ℝ) + a) ((k.val : ℝ) + b)) :
    supportAngleUpper (traceRotationBasis k.val) S -
        supportAngleLower (traceRotationBasis k.val) S ≤
      (traceBoundaryTurn
        (traceBoundaryOpenArc ((k.val : ℝ) + a) ((k.val : ℝ) + b))).toReal := by
  have hbounds := traceChord_supportAngleLower_upper_bounds k a b ha hab hb S hS hsub
  rw [traceBoundaryTurn_chord_openArc_toReal_eq k a b ha hab hb]
  exact sub_le_sub hbounds.2 hbounds.1

end Markov
