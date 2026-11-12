import Markov.TraceCyclicAtoms
import Markov.TraceBoundaryOpenArcs
import Markov.ShortNormalArc
import Markov.SupportAngleShortBranch

/-! The full actual turn of an open arc within a quadrant chord is
controlled by its two inward normal directions. The positive-sum half-plane
fixes the short branch, so the estimate includes all intervening turn. -/

noncomputable section
open Set MeasureTheory

namespace Markov

/-- The actual open boundary-arc mass is the difference between the
incoming right support angle and the outgoing left support angle. -/
theorem traceBoundaryTurn_chord_openArc_eq (k : Fin 4) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    traceBoundaryTurn (traceBoundaryOpenArc ((k.val : ℝ) + a) ((k.val : ℝ) + b)) =
      ENNReal.ofReal (chordLeftSelectedAngle (traceRotationBasis k.val) b -
        chordSelectedAngle (traceRotationBasis k.val) a) := by
  have hk : (k.val : ℝ) ≤ 3 := by exact_mod_cast (show k.val ≤ 3 by omega)
  rw [traceBoundaryTurn_openArc_eq _ _ (by positivity) (by linarith),
    traceCyclicAngleLift_leftLim_at_chord k b ⟨by linarith, hb⟩,
    traceCyclicAngleLift_at_chord k a ⟨ha, by linarith⟩,
    add_sub_add_right_eq_sub]

theorem traceBoundaryTurn_chord_openArc_toReal_eq (k : Fin 4) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    (traceBoundaryTurn
      (traceBoundaryOpenArc ((k.val : ℝ) + a) ((k.val : ℝ) + b))).toReal =
      chordLeftSelectedAngle (traceRotationBasis k.val) b -
        chordSelectedAngle (traceRotationBasis k.val) a := by
  have hm := traceCyclicAngleLift.mono.le_leftLim
    (show (k.val : ℝ) + a < (k.val : ℝ) + b by linarith)
  rw [traceCyclicAngleLift_at_chord k a ⟨ha, by linarith⟩,
    traceCyclicAngleLift_leftLim_at_chord k b ⟨by linarith, hb⟩] at hm
  rw [traceBoundaryTurn_chord_openArc_eq k a b ha hab hb,
    ENNReal.toReal_ofReal (by linarith)]

/-- The entire open arc's actual turn is at most `π/2` times the
Euclidean distance of its actual inward endpoint normals. -/
theorem traceBoundaryTurn_chord_openArc_le_inward_normal_distance
    (k : Fin 4) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    (traceBoundaryTurn
      (traceBoundaryOpenArc ((k.val : ℝ) + a) ((k.val : ℝ) + b))).toReal ≤
      (Real.pi / 2) *
        dist (normalizedEuclideanCovector traceBasis
          (chordSelectedSupport (traceRotationBasis k.val) a))
          (normalizedEuclideanCovector traceBasis
            (chordLeftSelectedSupport (traceRotationBasis k.val) b)) := by
  let B := traceRotationBasis k.val
  let f := chordSelectedSupport B a
  let g := chordLeftSelectedSupport B b
  have hfpos : 0 < f (B 0) + f (B 1) :=
    chordSelectedSupport_sum_pos B traceAxisLength a
      (norm_traceRotationBasis_zero k) (norm_traceRotationBasis_one k)
      (norm_traceRotationBasis_sub_lt k) ⟨ha, by linarith⟩
  have hgpos : 0 < g (B 0) + g (B 1) := by
    simpa only [map_add] using normingFunctional_sum_pos_on_equal_norm_chord
      (B 0) (B 1) traceAxisLength b
      (norm_traceRotationBasis_zero k) (norm_traceRotationBasis_one k)
      (norm_traceRotationBasis_sub_lt k) ⟨by linarith, hb⟩ g
      (chordLeftSelectedSupport_mem_normingFunctionals B b)
  have hfne : f ≠ 0 := by intro hz; simp [hz] at hfpos
  have hgne : g ≠ 0 := by intro hz; simp [hz] at hgpos
  have hshort := abs_supportAngle_sub_lt_pi_of_sum_pos B f g hfpos hgpos
  have hshort' : |(supportAngle B f + (k.val : ℝ) * Real.pi / 2) -
      (supportAngle B g + (k.val : ℝ) * Real.pi / 2)| ≤ Real.pi := by
    simpa only [add_sub_add_right_eq_sub] using hshort.le
  have hh := abs_sub_le_pi_div_two_mul_dist_circleNormal
    (supportAngle B f + (k.val : ℝ) * Real.pi / 2)
    (supportAngle B g + (k.val : ℝ) * Real.pi / 2) hshort'
  rw [show B = (quarterTurnBasis^[k.val]) traceBasis from rfl,
    circleNormal_supportAngle_iterate_quarterTurnBasis traceBasis f hfne k.val,
    circleNormal_supportAngle_iterate_quarterTurnBasis traceBasis g hgne k.val,
    add_sub_add_right_eq_sub] at hh
  rw [traceBoundaryTurn_chord_openArc_toReal_eq k a b ha hab hb]
  change supportAngle B g - supportAngle B f ≤ _
  have hleft : supportAngle B g - supportAngle B f ≤
      |supportAngle B f - supportAngle B g| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  exact hleft.trans hh

end Markov
