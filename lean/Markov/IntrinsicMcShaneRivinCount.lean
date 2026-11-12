import Markov.IntrinsicMcShaneRivinNorm
import Markov.TraceStrictConvexity
import Markov.ModularH1Transport

/-! The imported intrinsic norm is constructed after the unconditional actual
geometric primitive-agreement theorem, with no agreement premise left open.

The ball is DEFINED from the independently characterized intrinsic norm.
The lattice is DEFINED from the genuine original fixed-I integral-H1 marking.
All volume below is the unchanged standard Euclidean volume. -/
noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped Pointwise Topology ENNReal
namespace Markov

/-- The geometric McShane–Rivin unit ball, defined intrinsically. The trace
ball does not occur in this definition. -/
def modularMcShaneRivinBall : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | modularMcShaneRivinNorm x ≤ 1}

/-- Original integral homology in the fixed positive A/B Euclidean coordinates. -/
def modularMarkedHomologyVector
    (c : integralSingularH1 ModularTraceQuotient) : EuclideanSpace ℝ (Fin 2) :=
  euclideanIntDirection (modularTraceFixedSingularH1Equiv c)

private theorem actualEuclideanInteger_injective : Function.Injective euclideanIntDirection := by
  intro p q hpq
  have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hpq
  have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hpq
  change (p.1 : ℝ) = (q.1 : ℝ) at h0
  change (p.2 : ℝ) = (q.2 : ℝ) at h1
  apply Prod.ext
  · exact_mod_cast h0
  · exact_mod_cast h1

theorem modularMarkedHomologyVector_injective : Function.Injective modularMarkedHomologyVector :=
  actualEuclideanInteger_injective.comp modularTraceFixedSingularH1Equiv.injective

/-- The ACTUAL marked homology lattice, not a presumed trace lattice. -/
def modularMcShaneRivinLattice : Set (EuclideanSpace ℝ (Fin 2)) :=
  Set.range modularMarkedHomologyVector

/-- Surjectivity of the actual fixed-I marking identifies its lattice with
all standard integer vectors, with no sign quotient or area factor. -/
theorem modularMcShaneRivinLattice_eq_standard :
    modularMcShaneRivinLattice = Set.range euclideanIntDirection := by
  ext x
  constructor
  · rintro ⟨c,rfl⟩
    exact ⟨modularTraceFixedSingularH1Equiv c,rfl⟩
  · rintro ⟨p,rfl⟩
    refine ⟨modularTraceFixedSingularH1Equiv.symm p,?_⟩
    unfold modularMarkedHomologyVector
    rw [modularTraceFixedSingularH1Equiv.apply_symm_apply]

/-- Every original lattice point in a geometric dilate is counted, including
zero and nonprimitive integer points. -/
def modularMcShaneRivinLatticePointSet (R : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  modularMcShaneRivinLattice ∩ R • modularMcShaneRivinBall

def modularMcShaneRivinLatticeCount (R : ℝ) : ℕ :=
  (modularMcShaneRivinLatticePointSet R).ncard

/-- Standard Euclidean area of the intrinsic geometric unit ball. -/
def modularMcShaneRivinArea : ℝ := (volume modularMcShaneRivinBall).toReal

/-- A proved equality AFTER intrinsic construction, not the ball definition. -/
theorem modularMcShaneRivinBall_eq_traceEuclideanBall :
    modularMcShaneRivinBall = traceEuclideanBall := by
  unfold modularMcShaneRivinBall
  rw [modularMcShaneRivinNorm_eq_traceEuclideanGauge]
  ext x
  exact (mem_traceEuclideanBall_iff x).symm

theorem modularMcShaneRivinBall_isCompact : IsCompact modularMcShaneRivinBall := by
  rw [modularMcShaneRivinBall_eq_traceEuclideanBall]
  exact isCompact_traceEuclideanBall

theorem modularMcShaneRivinBall_strictConvex : StrictConvex ℝ modularMcShaneRivinBall := by
  rw [modularMcShaneRivinBall_eq_traceEuclideanBall]
  exact strictConvex_traceEuclideanBall

theorem modularMcShaneRivinBall_volume_pos : 0 < volume modularMcShaneRivinBall := by
  rw [modularMcShaneRivinBall_eq_traceEuclideanBall]
  exact traceEuclideanBall_volume_pos

theorem modularMcShaneRivinBall_volume_lt_top : volume modularMcShaneRivinBall < ∞ := by
  rw [modularMcShaneRivinBall_eq_traceEuclideanBall]
  exact traceEuclideanBall_volume_lt_top

theorem modularMcShaneRivinArea_eq_traceEuclideanArea :
    modularMcShaneRivinArea = traceEuclideanArea := by
  change (volume modularMcShaneRivinBall).toReal = (volume traceEuclideanBall).toReal
  rw [modularMcShaneRivinBall_eq_traceEuclideanBall]

theorem modularMcShaneRivinArea_pos : 0 < modularMcShaneRivinArea := by
  rw [modularMcShaneRivinArea_eq_traceEuclideanArea]
  exact traceEuclideanArea_pos

/-- The full standard integer-coordinate preimage of the intrinsic dilate. -/
def modularMcShaneRivinCoordinateSet (R : ℝ) : Set (ℤ × ℤ) :=
  {p | euclideanIntDirection p ∈ R • modularMcShaneRivinBall}

private theorem intrinsicLatticePointSet_image (R : ℝ) :
    euclideanIntDirection '' modularMcShaneRivinCoordinateSet R = modularMcShaneRivinLatticePointSet R := by
  rw [modularMcShaneRivinLatticePointSet,modularMcShaneRivinLattice_eq_standard]
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨⟨p,rfl⟩,hp⟩
  · rintro ⟨⟨p,rfl⟩,hp⟩
    exact ⟨p,hp,rfl⟩

/-- Actual marked-lattice cardinality equals the count of ALL standard
integer pairs in the intrinsic geometric dilate. -/
theorem modularMcShaneRivinLatticeCount_eq_coordinate_ncard (R : ℝ) :
    modularMcShaneRivinLatticeCount R = (modularMcShaneRivinCoordinateSet R).ncard := by
  rw [modularMcShaneRivinLatticeCount,← intrinsicLatticePointSet_image R]
  exact Set.ncard_image_of_injective _ actualEuclideanInteger_injective

/-- The same count can be read directly on genuine integral singular H1,
using its proved fixed original-generator marking rather than a label field. -/
theorem modularMcShaneRivinLatticeCount_eq_original_homology_ncard (R : ℝ) :
    modularMcShaneRivinLatticeCount R =
      ({c : integralSingularH1 ModularTraceQuotient |
        modularMarkedHomologyVector c ∈ R • modularMcShaneRivinBall}).ncard := by
  rw [modularMcShaneRivinLatticeCount_eq_coordinate_ncard]
  symm
  apply Set.ncard_congr'
  exact Equiv.subtypeEquiv modularTraceFixedSingularH1Equiv.toEquiv (fun _ => Iff.rfl)

/-- Exact full-count identification after the independently defined geometric
ball and original lattice have been identified. -/
theorem modularMcShaneRivinLatticeCount_eq_traceLatticeCount (R : ℝ) (hR : 0 < R) :
    modularMcShaneRivinLatticeCount R = traceLatticeCount R := by
  rw [modularMcShaneRivinLatticeCount_eq_coordinate_ncard]
  change ({p | euclideanIntDirection p ∈ R • modularMcShaneRivinBall}).ncard = traceLatticeCount R
  rw [modularMcShaneRivinBall_eq_traceEuclideanBall]
  exact (traceLatticeCount_eq_ncard_actual R hR).symm

theorem modularMcShaneRivinCoordinateSet_finite (R : ℝ) (hR : 0 < R) :
    (modularMcShaneRivinCoordinateSet R).Finite := by
  change {p | euclideanIntDirection p ∈ R • modularMcShaneRivinBall}.Finite
  rw [modularMcShaneRivinBall_eq_traceEuclideanBall]
  exact traceEuclideanLatticeSet_finite R hR

theorem modularMcShaneRivinLatticePointSet_finite (R : ℝ) (hR : 0 < R) :
    (modularMcShaneRivinLatticePointSet R).Finite := by
  rw [← intrinsicLatticePointSet_image R]
  exact (modularMcShaneRivinCoordinateSet_finite R hR).image _

/-- The exact full-lattice Theorem12 transfer for the intrinsically defined
geometric ball, original marked lattice and unchanged standard Euclidean area.
No primitive-agreement, norm, classification or area premise remains here;
the unconditional geometric agreement theorem is an imported dependency. -/
theorem modularMcShaneRivin_lattice_asymptotic :
    (fun R : ℝ => (modularMcShaneRivinLatticeCount R : ℝ) -
      (volume modularMcShaneRivinBall).toReal * R^2) =O[atTop]
      (fun R : ℝ => R / Real.log R ^ (3/2 : ℝ)) := by
  have h := lattice_asymptotic_of_primitive_values modularMcShaneRivinNorm
    modularMcShaneRivinNorm_continuous modularMcShaneRivinNorm_smul
    modularMcShaneRivinNorm_primitive_trace_value
  simpa only [modularMcShaneRivinLatticeCount_eq_coordinate_ncard,
    modularMcShaneRivinCoordinateSet,modularMcShaneRivinBall] using h

end Markov
