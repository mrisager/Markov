import Markov.ChordCornerGeometry
import Markov.TraceBoundaryInjective
import Markov.TraceCyclicNormals

/-! The complete actual normal fibre at every point of a closed trace
chord is the closed circular arc between its incoming and outgoing support
angles. Quarter-turn offsets place this arc in the original Euclidean
trace coordinates, including all axis seams. -/

noncomputable section
open Set

namespace Markov

/-- Radial normalization preserves the whole norming-support fibre of a
trace chord, including both endpoints. -/
theorem traceBoundaryPath_normingFunctionals_eq_chord (i : Fin 4) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    normingFunctionals (traceBoundaryPath ((i.val : ℝ) + s)) =
      normingFunctionals ((1 - s) • traceRotationBasis i.val 0 +
        s • traceRotationBasis i.val 1) := by
  rw [traceBoundaryPath_add_eq_chordBoundarySection i s hs,
    chordBoundarySection, radialBasisSection,
    normingFunctionals_normalize_eq _
      (basis_affineLine_ne_zero (chordBasis (traceRotationBasis i.val)) s),
    chordBasis_affinePoint]

/-- All principal support angles at a path point fill the interval between
the actual incoming and outgoing selections in its own chord frame. -/
theorem traceBoundaryPath_corner_supportAngles_eq_Icc (i : Fin 4) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    supportAngle (traceRotationBasis i.val) ''
        normingFunctionals (traceBoundaryPath ((i.val : ℝ) + s)) =
      Icc (chordLeftSelectedAngle (traceRotationBasis i.val) s)
        (chordSelectedAngle (traceRotationBasis i.val) s) := by
  rw [traceBoundaryPath_normingFunctionals_eq_chord i s hs]
  exact chord_supportAngles_eq_Icc (traceRotationBasis i.val) traceAxisLength s
    (norm_traceRotationBasis_zero i) (norm_traceRotationBasis_one i)
    (norm_traceRotationBasis_sub_lt i) hs

/-- The full actual normal fibre is exactly the circular arc from incoming
to outgoing support, expressed in the original Euclidean trace frame. -/
theorem traceBoundaryPath_corner_normals_eq_arc (i : Fin 4) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    normalsOn traceBasis {traceBoundaryPath ((i.val : ℝ) + s)} =
      circleNormal '' Icc
        (chordLeftSelectedAngle (traceRotationBasis i.val) s +
          (i.val : ℝ) * Real.pi / 2)
        (chordSelectedAngle (traceRotationBasis i.val) s +
          (i.val : ℝ) * Real.pi / 2) := by
  have hpath : traceBoundaryPath ((i.val : ℝ) + s) ≠ 0 := by
    intro hz
    have hn := norm_traceBoundaryPath ((i.val : ℝ) + s)
    simp [hz] at hn
  have hangles := traceBoundaryPath_corner_supportAngles_eq_Icc i s hs
  ext n
  constructor
  · rintro ⟨x, hx, f, hf, hn⟩
    rcases mem_singleton_iff.mp hx with rfl
    have hfangle : supportAngle (traceRotationBasis i.val) f ∈
        Icc (chordLeftSelectedAngle (traceRotationBasis i.val) s)
          (chordSelectedAngle (traceRotationBasis i.val) s) := by
      rw [← hangles]
      exact ⟨f, hf, rfl⟩
    refine ⟨supportAngle (traceRotationBasis i.val) f +
      (i.val : ℝ) * Real.pi / 2,
      by constructor <;> linarith only [hfangle.1, hfangle.2], ?_⟩
    exact (circleNormal_supportAngle_iterate_quarterTurnBasis traceBasis f
      (normingFunctional_ne_zero _ hpath f hf) i.val).trans hn.symm
  · rintro ⟨θ, hθ, rfl⟩
    have hlocal : θ - (i.val : ℝ) * Real.pi / 2 ∈
        Icc (chordLeftSelectedAngle (traceRotationBasis i.val) s)
          (chordSelectedAngle (traceRotationBasis i.val) s) := by
      constructor <;> linarith [hθ.1, hθ.2]
    rw [← hangles] at hlocal
    obtain ⟨f, hf, hfangle⟩ := hlocal
    refine ⟨traceBoundaryPath ((i.val : ℝ) + s), mem_singleton _, f, hf, ?_⟩
    have hθeq : θ = supportAngle (traceRotationBasis i.val) f +
        (i.val : ℝ) * Real.pi / 2 := by
      linarith only [hfangle]
    rw [hθeq]
    exact circleNormal_supportAngle_iterate_quarterTurnBasis traceBasis f
      (normingFunctional_ne_zero _ hpath f hf) i.val

end Markov
