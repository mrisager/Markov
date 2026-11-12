import Markov.TraceCyclicTurn
import Markov.TraceBoundaryPath

/-! The cyclic support-angle lift represents actual normals to the actual
trace-boundary path. The witnesses are the selected chord functionals in
the original trace norm. No full normal-fibre or normal-arc equality is
asserted. -/

noncomputable section
open Set

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Chord selection remains an actual norming support after radial
normalization of the chord point. -/
theorem chordSelectedSupport_mem_norming_radialBasisSection
    (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) :
    chordSelectedSupport B s ∈ normingFunctionals (radialBasisSection (chordBasis B) s) := by
  rw [radialBasisSection,
    normingFunctionals_normalize_eq _ (basis_affineLine_ne_zero (chordBasis B) s),
    chordBasis_affinePoint]
  exact chordSelectedSupport_mem_normingFunctionals B s

theorem chordSelectedSupport_ne_zero (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) :
    chordSelectedSupport B s ≠ 0 := by
  apply normingFunctional_basisLine_ne_zero (chordBasis B) s
  rw [chordBasis_affinePoint]
  exact chordSelectedSupport_mem_normingFunctionals B s

/-- Each shifted local lift has exactly the normalized Euclidean covector
of its actual selected support, in the original trace coordinates. -/
theorem circleNormal_traceShiftedChordLift (i : Fin 4) (t : ℝ)
    (ht : t - (i.val : ℝ) ∈ Icc (0 : ℝ) 1) :
    circleNormal (traceShiftedChordLift i t) =
      normalizedEuclideanCovector traceBasis
        (chordSelectedSupport (traceRotationBasis i.val) (t - (i.val : ℝ))) := by
  rw [traceShiftedChordLift_apply, traceChordAngleLift_eq_chord i _ ht,
    chordSelectedAngle]
  exact circleNormal_supportAngle_iterate_quarterTurnBasis traceBasis _
    (chordSelectedSupport_ne_zero _ _) i.val

/-- The actual selected functional on each of the four path pieces, with
seams assigned to the piece on their right as in the boundary path. -/
def traceCyclicSelectedSupport (t : ℝ) : StrongDual ℝ TracePlane :=
  if t < 1 then chordSelectedSupport (traceRotationBasis 0) t
  else if t < 2 then chordSelectedSupport (traceRotationBasis 1) (t - 1)
  else if t < 3 then chordSelectedSupport (traceRotationBasis 2) (t - 2)
  else chordSelectedSupport (traceRotationBasis 3) (t - 3)

/-- The selected witness norms the actual boundary point for every real
parameter, including the extended chord pieces outside one period. -/
theorem traceCyclicSelectedSupport_mem_normingFunctionals (t : ℝ) :
    traceCyclicSelectedSupport t ∈ normingFunctionals (traceBoundaryPath t) := by
  unfold traceCyclicSelectedSupport traceBoundaryPath
  split_ifs <;> exact chordSelectedSupport_mem_norming_radialBasisSection _ _

theorem traceCyclicSelectedSupport_ne_zero (t : ℝ) : traceCyclicSelectedSupport t ≠ 0 := by
  have hpath : traceBoundaryPath t ≠ 0 := by
    intro hz
    have hn := norm_traceBoundaryPath t
    simp [hz] at hn
  exact normingFunctional_ne_zero _ hpath _
    (traceCyclicSelectedSupport_mem_normingFunctionals t)

/-- On one closed period, the glued real angle is the actual normal of
the selected norming functional at the actual boundary point. -/
theorem circleNormal_traceCyclicAngleLift (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) :
    circleNormal (traceCyclicAngleLift t) =
      normalizedEuclideanCovector traceBasis (traceCyclicSelectedSupport t) := by
  by_cases h1 : t < 1
  · rw [traceCyclicAngleLift_of_lt_one t h1]
    simp only [traceCyclicSelectedSupport, if_pos h1]
    simpa using circleNormal_traceShiftedChordLift 0 t (by
      simp only [Fin.val_zero, Nat.cast_zero, sub_zero, mem_Icc]
      exact ⟨ht.1, h1.le⟩)
  · have h1' : 1 ≤ t := le_of_not_gt h1
    by_cases h2 : t < 2
    · rw [traceCyclicAngleLift_of_one_le_of_lt_two t h1' h2]
      simp only [traceCyclicSelectedSupport, if_neg h1, if_pos h2]
      simpa using circleNormal_traceShiftedChordLift 1 t (by
        simp only [Fin.val_one, Nat.cast_one, mem_Icc]
        constructor <;> linarith)
    · have h2' : 2 ≤ t := le_of_not_gt h2
      by_cases h3 : t < 3
      · rw [traceCyclicAngleLift_of_two_le_of_lt_three t h2' h3]
        simp only [traceCyclicSelectedSupport, if_neg h1, if_neg h2, if_pos h3]
        simpa using circleNormal_traceShiftedChordLift 2 t (by
          change 0 ≤ t - (2 : ℝ) ∧ t - 2 ≤ 1
          constructor <;> linarith)
      · have h3' : 3 ≤ t := le_of_not_gt h3
        rw [traceCyclicAngleLift_of_three_le t h3']
        simp only [traceCyclicSelectedSupport, if_neg h1, if_neg h2, if_neg h3]
        simpa using circleNormal_traceShiftedChordLift 3 t (by
          change 0 ≤ t - (3 : ℝ) ∧ t - 3 ≤ 1
          constructor <;> linarith [ht.2])

/-- An explicit actual-support witness for the cyclic normal, rather than
an assumed containment of abstract angle parameters. -/
theorem traceCyclicAngleLift_exists_normingFunctional (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 4) :
    ∃ f ∈ normingFunctionals (traceBoundaryPath t), f ≠ 0 ∧
      circleNormal (traceCyclicAngleLift t) = normalizedEuclideanCovector traceBasis f :=
  ⟨traceCyclicSelectedSupport t, traceCyclicSelectedSupport_mem_normingFunctionals t,
    traceCyclicSelectedSupport_ne_zero t, circleNormal_traceCyclicAngleLift t ht⟩

/-- The glued cyclic angle is a genuine normal at its corresponding
actual trace-boundary point, including all quarter seams. -/
theorem circleNormal_traceCyclicAngleLift_mem_normalsOn (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 4) :
    circleNormal (traceCyclicAngleLift t) ∈ normalsOn traceBasis {traceBoundaryPath t} :=
  ⟨traceBoundaryPath t, mem_singleton _, traceCyclicSelectedSupport t,
    traceCyclicSelectedSupport_mem_normingFunctionals t,
    circleNormal_traceCyclicAngleLift t ht⟩

end Markov
