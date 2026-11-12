import Markov.PrimitiveAxisTraceNorm
import Markov.IntrinsicSimpleGeodesicLengths
import Markov.ModularSimpleMetricCircleNormalDiagramH1

/-! Primitive geometric length agreement. The primitive-axis period
theorem identifies all simple-geodesic lengths in each primitive marked
homology class with the trace-norm value. -/

noncomputable section
open Set Topology
namespace Markov

/-- ALL actual simple locally unit-speed period circles in an original
primitive H1 class have exactly the canonical length. The set was defined
independently of trace words and is not restricted to canonical witnesses. -/
theorem modularSimpleGeodesicLengthSet_eq_singleton (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    modularSimpleGeodesicLengthSet p = {‖intVector traceBasis p‖} := by
  ext L
  constructor
  · rintro ⟨hpos, q, hq, _, hlocal, hclass⟩
    obtain ⟨D, hD, c, a, hlen, _, _, hoff, _, hproject,
      _, _, _, _, _, _, hcoord⟩ :=
      modularSimpleMetricCircle_finite_Q_itinerary_coordinates L hpos q hq hlocal
    have hcoords : (paperTraceAbelianizationCoordinates D).toAdd = p :=
      (paperAxisPeriodCellWord_signedSum D hD a hoff).symm.trans (hcoord.trans hclass)
    have hpD : IsCoprime (paperTraceAbelianizationCoordinates D).toAdd.1
        (paperTraceAbelianizationCoordinates D).toAdd.2 := by
      rw [hcoords]
      exact hp
    have hper := paperAxisPrimitive_period_eq_trace_norm D hD a hoff hproject hpD
    rw [hcoords] at hper
    exact Set.mem_singleton_iff.mpr (hlen.symm.trans hper)
  · intro hL
    rw [Set.mem_singleton_iff] at hL
    rw [hL]
    exact trace_norm_mem_modularSimpleGeodesicLengthSet p hp

/-- The independently defined intrinsic infimum agrees with the trace norm
because every actual member has that value and the canonical member exists. -/
theorem modularSimpleGeodesicLengthInf_eq_trace_norm (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    modularSimpleGeodesicLengthInf p = ‖intVector traceBasis p‖ := by
  unfold modularSimpleGeodesicLengthInf
  rw [modularSimpleGeodesicLengthSet_eq_singleton p hp, csInf_singleton]

end Markov
