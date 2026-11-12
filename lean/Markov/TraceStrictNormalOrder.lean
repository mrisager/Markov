import Markov.PrimitiveRationalDensity
import Markov.TraceCornerEstimate
import Markov.TraceBoundaryNormalAngles

/-! Strict ordering of complete normal fibres on one actual boundary traversal.
The lift is used only on its single period; no periodic extension is assumed. -/

noncomputable section
open Set MeasureTheory

namespace Markov

/-- Primitive rational corners force strict separation between the outgoing
angle at an earlier point and the incoming angle at a later point. -/
theorem traceCyclicAngleLift_lt_leftLim {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 4) :
    traceCyclicAngleLift a < Function.leftLim traceCyclicAngleLift b := by
  obtain ⟨k, p, hpc, hp0, hp1, hpa, hpb⟩ :=
    exists_primitive_traceRationalParameter_between ha hab hb
  have hp : NonnegativePrimitiveDirection (quadrantCoordinates k p) :=
    ⟨hp0.le, hp1.le, quadrantCoordinates_coprime k p hpc⟩
  have hpath := traceBoundaryPath_traceRationalParameter k p hp0.le hp1.le
    (profileMass_pos _ hp)
  have ht : traceRationalParameter k p ∈ Ioc (0 : ℝ) 4 :=
    ⟨ha.trans_lt hpa, hpb.le.trans hb⟩
  have hjump := primitive_trace_atom_pos p hpc
  rw [← hpath, traceBoundaryTurn_singleton_toReal_eq_jump _ ht] at hjump
  exact (traceCyclicAngleLift.mono.le_leftLim hpa).trans_lt
    ((sub_pos.mp hjump).trans_le (traceCyclicAngleLift.mono.le_leftLim hpb))

/-- The actual outgoing normal-angle lift is strictly increasing on its period. -/
theorem traceCyclicAngleLift_strictMonoOn :
    StrictMonoOn traceCyclicAngleLift (Icc (0 : ℝ) 4) := by
  intro a ha b hb hab
  exact (traceCyclicAngleLift_lt_leftLim ha.1 hab hb.2).trans_le
    (traceCyclicAngleLift.mono.leftLim_le le_rfl)

/-- All angles in an earlier complete normal fibre lie strictly below all
angles in a later fibre. -/
theorem trace_complete_normal_angles_lt {a b θ φ : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 4)
    (hθ : θ ∈ Icc (Function.leftLim traceCyclicAngleLift a) (traceCyclicAngleLift a))
    (hφ : φ ∈ Icc (Function.leftLim traceCyclicAngleLift b) (traceCyclicAngleLift b)) :
    θ < φ :=
  hθ.2.trans_lt ((traceCyclicAngleLift_lt_leftLim ha hab hb).trans_le hφ.1)

/-- On the half-open boundary period, distinct normal fibres are separated
by strictly less than one full turn as well as by a positive angle. -/
theorem trace_complete_normal_angles_sub_lt_two_pi {a b θ φ : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 4)
    (hθ : θ ∈ Icc (Function.leftLim traceCyclicAngleLift a) (traceCyclicAngleLift a))
    (hφ : φ ∈ Icc (Function.leftLim traceCyclicAngleLift b) (traceCyclicAngleLift b)) :
    φ - θ < 2 * Real.pi := by
  have hstart := traceCyclicAngleLift_lt_leftLim (by norm_num : (0 : ℝ) ≤ 0) ha
    (hab.le.trans hb)
  have hend := traceCyclicAngleLift.mono hb
  linarith [traceCyclicAngleLift_period_increment, hθ.1, hφ.2]

/-- Two circle normals with an angle difference strictly between zero and
one full turn cannot agree. -/
theorem circleNormal_ne_of_lt_of_sub_lt_two_pi {θ φ : ℝ}
    (hθφ : θ < φ) (hwidth : φ - θ < 2 * Real.pi) :
    circleNormal θ ≠ circleNormal φ := by
  intro heq
  have hcos : Real.cos θ = Real.cos φ := by
    simpa only [circleNormal, Matrix.cons_val_zero] using
      congrArg (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 0) heq
  have hsin : Real.sin θ = Real.sin φ := by
    simpa only [circleNormal, Matrix.cons_val_one, Matrix.cons_val_zero] using
      congrArg (fun z : EuclideanSpace ℝ (Fin 2) ↦ z 1) heq
  have hdiff : Real.cos (φ - θ) = 1 := by
    rw [Real.cos_sub, ← hcos, ← hsin]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hz := (Real.cos_eq_one_iff_of_lt_of_lt
    (by linarith [Real.pi_pos] : -(2 * Real.pi) < φ - θ) hwidth).mp hdiff
  linarith

/-- Complete normal fibres of distinct path points in one half-open
traversal are disjoint on the circle. -/
theorem traceBoundaryPath_normals_disjoint {a b : ℝ}
    (ha : a ∈ Ioc (0 : ℝ) 4) (hb : b ∈ Ioc (0 : ℝ) 4) (hab : a ≠ b) :
    Disjoint (normalsOn traceBasis {traceBoundaryPath a})
      (normalsOn traceBasis {traceBoundaryPath b}) := by
  have hordered {s t : ℝ} (hs : s ∈ Ioc (0 : ℝ) 4)
      (ht : t ∈ Ioc (0 : ℝ) 4) (hst : s < t) :
      Disjoint (normalsOn traceBasis {traceBoundaryPath s})
        (normalsOn traceBasis {traceBoundaryPath t}) := by
    rw [traceBoundaryPath_normals_eq_lift_arc s hs, traceBoundaryPath_normals_eq_lift_arc t ht]
    apply Set.disjoint_left.mpr
    rintro n ⟨θ, hθ, rfl⟩ ⟨φ, hφ, heq⟩
    exact circleNormal_ne_of_lt_of_sub_lt_two_pi
      (trace_complete_normal_angles_lt hs.1.le hst ht.2 hθ hφ)
      (trace_complete_normal_angles_sub_lt_two_pi hs.1 hst ht.2 hθ hφ) heq.symm
  rcases lt_or_gt_of_ne hab with hab' | hab'
  · exact hordered ha hb hab'
  · exact (hordered hb ha hab').symm

/-- A genuine normal direction can belong to only one actual unit-boundary point. -/
theorem traceBoundary_normal_point_unique {x y : TracePlane}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {n : EuclideanSpace ℝ (Fin 2)}
    (hnx : n ∈ normalsOn traceBasis {x}) (hny : n ∈ normalsOn traceBasis {y}) : x = y := by
  obtain ⟨a, ha, rfl⟩ := traceBoundaryPath_exists_Ioc x hx
  obtain ⟨b, hb, rfl⟩ := traceBoundaryPath_exists_Ioc y hy
  by_cases hab : a = b
  · rw [hab]
  · exact False.elim (Set.disjoint_left.mp (traceBoundaryPath_normals_disjoint ha hb hab) hnx hny)

end Markov
