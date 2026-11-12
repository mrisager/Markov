import Markov.TraceBoundaryCoverage
import Markov.TraceBoundaryTurn
import Markov.TraceFullCornerArc
import Markov.TraceCyclicAtoms

/-! Exact singleton transport for the actual boundary measure. Injectivity
on the half-open period proves the preimage identity, including the initial
point represented at parameter 4. Geometric corner widths are linked to
the Stieltjes jumps below without a quantitative lower-bound assumption. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Markov

theorem traceBoundaryTurn_singleton_eq_parameter (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 4) :
    traceBoundaryTurn {traceBoundaryPath t} = angleTurnMeasure traceCyclicAngleLift {t} := by
  rw [traceBoundaryTurn_apply_eq_parameter_turn _ (measurableSet_singleton _),
    traceBoundaryPath_preimage_singleton_inter_Ioc t ht]

theorem traceBoundaryTurn_singleton_eq_jump (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 4) :
    traceBoundaryTurn {traceBoundaryPath t} =
      ENNReal.ofReal (traceCyclicAngleLift t - Function.leftLim traceCyclicAngleLift t) := by
  rw [traceBoundaryTurn_singleton_eq_parameter t ht, angleTurnMeasure_singleton]

theorem traceBoundaryTurn_singleton_toReal_eq_jump (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 4) :
    (traceBoundaryTurn {traceBoundaryPath t}).toReal =
      traceCyclicAngleLift t - Function.leftLim traceCyclicAngleLift t := by
  rw [traceBoundaryTurn_singleton_eq_parameter t ht,
    angleTurnMeasure_singleton_toReal traceCyclicAngleLift t]

theorem traceBoundaryTurn_singleton_exists_parameter (x : TracePlane) (hx : ‖x‖ = 1) :
    ∃ t ∈ Ioc (0 : ℝ) 4, traceBoundaryPath t = x ∧
      traceBoundaryTurn {x} =
        ENNReal.ofReal (traceCyclicAngleLift t - Function.leftLim traceCyclicAngleLift t) := by
  obtain ⟨t, ht, htx⟩ := traceBoundaryPath_exists_Ioc x hx
  exact ⟨t, ht, htx, htx ▸ traceBoundaryTurn_singleton_eq_jump t ht⟩

/-- Every complete normal fibre, including the initial axis represented
at parameter four, is exactly the angular interval of the actual lift's
jump. This identifies all supports rather than a selected witness. -/
theorem traceBoundaryPath_normals_eq_lift_arc (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 4) :
    normalsOn traceBasis {traceBoundaryPath t} =
      circleNormal '' Icc (Function.leftLim traceCyclicAngleLift t) (traceCyclicAngleLift t) := by
  obtain ⟨i, s, hs, rfl⟩ := exists_traceBoundary_quarter t ht
  rw [traceCyclicAngleLift_leftLim_at_chord i s hs,
    traceCyclicAngleLift_at_chord i s ⟨hs.1.le, hs.2⟩]
  exact traceBoundaryPath_corner_normals_eq_arc i s ⟨hs.1.le, hs.2⟩

/-- The actual boundary singleton mass is the angular length of its full
normal fibre, with the same real lift interval used in the fibre identity. -/
theorem traceBoundaryTurn_singleton_eq_angular_length (t : ℝ)
    (ht : t ∈ Ioc (0 : ℝ) 4) :
    traceBoundaryTurn {traceBoundaryPath t} =
      volume (Icc (Function.leftLim traceCyclicAngleLift t) (traceCyclicAngleLift t)) := by
  rw [traceBoundaryTurn_singleton_eq_jump t ht, Real.volume_Icc]

/-- Every actual boundary point has an interval describing all of its
normal directions whose angular length is its actual boundary turn atom. -/
theorem traceBoundaryTurn_full_normal_fibre (x : TracePlane) (hx : ‖x‖ = 1) :
    ∃ a b : ℝ, a ≤ b ∧ normalsOn traceBasis {x} = circleNormal '' Icc a b ∧
      traceBoundaryTurn {x} = volume (Icc a b) := by
  obtain ⟨t, ht, rfl⟩ := traceBoundaryPath_exists_Ioc x hx
  exact ⟨Function.leftLim traceCyclicAngleLift t, traceCyclicAngleLift t,
    traceCyclicAngleLift.mono.leftLim_le le_rfl,
    traceBoundaryPath_normals_eq_lift_arc t ht,
    traceBoundaryTurn_singleton_eq_angular_length t ht⟩

theorem traceBoundaryTurn_singleton_at_chord (i : Fin 4) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    traceBoundaryTurn {traceBoundaryPath ((i.val : ℝ) + s)} =
      ENNReal.ofReal (chordSelectedAngle (traceRotationBasis i.val) s -
        chordLeftSelectedAngle (traceRotationBasis i.val) s) := by
  have hi : (i.val : ℝ) ≤ 3 := by exact_mod_cast (show i.val ≤ 3 by omega)
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  rw [traceBoundaryTurn_singleton_eq_parameter _ ⟨by linarith [hs.1], by linarith [hs.2]⟩]
  exact traceCyclicTurn_singleton_at_chord i s hs

end Markov
