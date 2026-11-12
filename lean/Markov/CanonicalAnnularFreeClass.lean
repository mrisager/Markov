import Markov.AnnularOriginalClassHomotopy
import Markov.CanonicalAffineFreeClass
import Markov.CircleHomotopyLoopConjugacy

noncomputable section
open Topology
namespace Markov

/-- An actual circle-map homotopy transports the actual center connector by
the reversed basepoint path, preserving the genuine based loop class. -/
theorem circleHomotopy_basedLoop_connector
    {q0 q1 : C(NormalizedCircle, ModularTraceQuotient)} (H : q0.Homotopy q1)
    (d : Path paperGeneratorCenterPoint (q1 0)) :
    (embeddedCircleBasedLoop q0 q0.continuous
      (d.trans (normalizedCircleHomotopyBasePath H).symm)).Homotopic
        (embeddedCircleBasedLoop q1 q1.continuous d) := by
  have hc {x y z : ModularTraceQuotient}
      (a : Path.Homotopic.Quotient x y) (b : Path.Homotopic.Quotient y z) :
      a.symm.trans (a.trans b) = b := by
    rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.refl_trans]
  apply Path.Homotopic.Quotient.eq.mp
  simp only [embeddedCircleBasedLoop, Path.trans_symm, Path.symm_symm,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  rw [normalizedCircleHomotopy_positiveLoop_quotient H]
  simp only [Path.Homotopic.Quotient.trans_assoc, hc]

/-- WITH actual primitive through-zero annulus containment and prescribed
original H1, the actual positive loop has the exact canonical nonabelian class. -/
theorem modularCircleMap_annular_canonical_marked
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p))
    (q : C(NormalizedCircle, ModularTraceQuotient))
    (hcontain : ∀ u, standardTorusSecondDual (originalToStandardCircleLabel p)
      (modularTraceQuotientPuncturedTorusHomeomorph (q u)).val ≠ 0)
    (hclass : modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient (normalizedCircleStandardLoop.map q.continuous)) = p) :
    ∃ e : Path paperGeneratorCenterPoint (q 0),
      modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
        (FundamentalGroup.fromPath (.mk (embeddedCircleBasedLoop q q.continuous e))) =
          (quadrantPrimitiveTraceWord k p hp)⁻¹ := by
  obtain ⟨a, ha, d, hm⟩ := quadrantPrimitiveTraceWord_inverse_has_affineRepresentative k p hp
  obtain ⟨H⟩ := modularCircleMap_homotopic_affine_of_annular_containment
    p a ha q hcontain hclass standardCircleHalf standardCircleHalf_ne_zero
  let e := d.trans (normalizedCircleHomotopyBasePath H).symm
  have he := circleHomotopy_basedLoop_connector H d
  refine ⟨e, ?_⟩
  exact (congrArg (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift)
    (congrArg FundamentalGroup.fromPath (Path.Homotopic.Quotient.eq.mpr he))).trans hm

/-- The conditional annular classification is an actual based geometric
homotopy to the canonical forward free class, with the actual connector. -/
theorem modularCircleMap_annular_canonical_homotopy
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p))
    (q : C(NormalizedCircle, ModularTraceQuotient))
    (hcontain : ∀ u, standardTorusSecondDual (originalToStandardCircleLabel p)
      (modularTraceQuotientPuncturedTorusHomeomorph (q u)).val ≠ 0)
    (hclass : modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient (normalizedCircleStandardLoop.map q.continuous)) = p) :
    ∃ e : Path paperGeneratorCenterPoint (q 0),
      (paperPrimitiveAxisTransportLoop k p hp).Homotopic
        (embeddedCircleBasedLoop q q.continuous e) := by
  obtain ⟨e, hm⟩ := modularCircleMap_annular_canonical_marked k p hp q hcontain hclass
  refine ⟨e, ?_⟩
  have he : FundamentalGroup.fromPath (.mk (paperPrimitiveAxisTransportLoop k p hp)) =
      FundamentalGroup.fromPath (.mk (embeddedCircleBasedLoop q q.continuous e)) :=
    (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).injective
      ((paperPrimitiveAxisTransportLoop_marked k p hp).trans hm.symm)
  exact Path.Homotopic.Quotient.eq.mp he

end Markov
