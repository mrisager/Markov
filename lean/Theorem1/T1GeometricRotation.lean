import T1LatticeRotationCoordinates
import T1AmbientAxisSimplicity
import T1GeometricThreshold
import Markov.CanonicalTraceNormPeriods
import Markov.CanonicalAxisDeckSeparation
import Markov.IntegerPeriodOpenIntervalInjectivity

/-! Genuine geometric primitive lengths are invariant under the actual
marked order-six modular rotation. Simplicity is transported geometrically,
then the proved intrinsic primitive-period theorem is applied. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace Markov

theorem t1_geometricLength_rotation (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    t1_geometricLength (t1_latticeRotation p) = t1_geometricLength p := by
  obtain ⟨k,hk1,hk2⟩ := exists_nonnegative_quadrantCoordinates p
  let hq : NonnegativePrimitiveDirection (quadrantCoordinates k p) :=
    ⟨hk1,hk2,quadrantCoordinates_coprime k p hp⟩
  let g := paperPrimitiveHolonomy k p hq
  have hg : 2 < |(g.val : IntMatrixTwo).trace| := paperPrimitiveHolonomy_hyperbolic k p hq
  have hc : paperTraceAbelianizationCoordinates g = Multiplicative.ofAdd p :=
    paperPrimitiveHolonomy_coordinates k p hq
  have hproj : ∀ b : ℝ, Set.InjOn
      (fun t : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg t))
      (Ioo b (b+modularClosedGeodesicPeriod g)) := by
    intro b
    exact integerPeriodEquality_injOn_Ioo (modularClosedGeodesicPeriod g)
      (modularClosedGeodesicPeriod_pos g hg) (paperPrimitiveClosedGeodesic k p hq)
      (paperPrimitiveClosedGeodesic_eq_iff_int_period k p hq) b
  have hrc : paperTraceAbelianizationCoordinates (t1_ambientConjugation ModularGroup.T g) =
      Multiplicative.ofAdd (t1_latticeRotation p) := by
    rw [t1_ambient_T_marked_coordinates,hc]
    rfl
  have hrot := t1_latticeRotation_coprime p hp
  have hp' : IsCoprime
      (paperTraceAbelianizationCoordinates (t1_ambientConjugation ModularGroup.T g)).toAdd.1
      (paperTraceAbelianizationCoordinates (t1_ambientConjugation ModularGroup.T g)).toAdd.2 := by
    rw [hrc]
    exact hrot
  have he := t1_ambientConjugation_period_eq_primitive_norm ModularGroup.T g hg hproj hp'
  rw [hrc] at he
  have he0 : modularClosedGeodesicPeriod g = ‖intVector traceBasis p‖ :=
    paperPrimitiveHolonomy_period_eq_trace_norm k p hq
  change modularMcShaneRivinNorm (euclideanIntDirection (t1_latticeRotation p)) =
    modularMcShaneRivinNorm (euclideanIntDirection p)
  rw [modularMcShaneRivinNorm_primitive_trace_value _ hrot,
    modularMcShaneRivinNorm_primitive_trace_value _ hp]
  exact he.symm.trans he0

end Markov
