import Markov.CanonicalEmbeddedCircles

/-! Actual reversal of a closed embedded circle and its exact nonabelian based
class. This supplies reversed raw canonical representatives without asserting
simplicity of the corresponding hyperbolic axis. -/

noncomputable section
open Topology
namespace Markov

/-- The literal circle orientation reversal u↦q(-u). -/
def reversedEmbeddedCircle {X : Type*} (q : NormalizedCircle → X) : NormalizedCircle → X :=
  fun u => q (-u)

@[simp] theorem reversedEmbeddedCircle_zero {X : Type*} (q : NormalizedCircle → X) :
    reversedEmbeddedCircle q 0 = q 0 := by simp [reversedEmbeddedCircle]

/-- Reversal preserves the genuine closed-embedding property. -/
theorem reversedEmbeddedCircle_isClosedEmbedding {X : Type*} [TopologicalSpace X]
    {q : NormalizedCircle → X} (hq : IsClosedEmbedding q) :
    IsClosedEmbedding (reversedEmbeddedCircle q) :=
  hq.comp (Homeomorph.neg NormalizedCircle).isClosedEmbedding

/-- The original actual connector, with its endpoint displayed at q(-0). -/
def reversedEmbeddedCircleConnector {X : Type*} [TopologicalSpace X] {x : X}
    (q : NormalizedCircle → X) (d : Path x (q 0)) :
    Path x (reversedEmbeddedCircle q 0) :=
  d.cast rfl (reversedEmbeddedCircle_zero q)

/-- The actual positive once-around circle path with the actual connector and reversal. -/
def embeddedCircleBasedLoop {X : Type*} [TopologicalSpace X] {x : X}
    (q : NormalizedCircle → X) (hq : Continuous q) (d : Path x (q 0)) : Path x x :=
  (d.trans (normalizedCircleStandardLoop.map hq)).trans d.symm

/-- Literal reversal of the normalized positive once-around circle loop. -/
theorem normalizedCircleStandardLoop_symm_apply (t : unitInterval) :
    normalizedCircleStandardLoop.symm t = -normalizedCircleStandardLoop t := by
  change normalizedCircleStandardLoop (unitInterval.symm t) = -normalizedCircleStandardLoop t
  rw [normalizedCircleStandardLoop_apply, normalizedCircleStandardLoop_apply]
  change (((1-(t : ℝ) : ℝ)) : NormalizedCircle) = -((t : ℝ) : NormalizedCircle)
  change (((1 : ℝ) : NormalizedCircle) - ((t : ℝ) : NormalizedCircle)) = _
  rw [AddCircle.coe_period, zero_sub]

/-- Reversing the embedded circle inverts its genuine based fundamental-group class,
with the same actual connector and only its proved endpoint cast. -/
theorem reversedEmbeddedCircleBasedLoop_class {X : Type*} [TopologicalSpace X] {x : X}
    (q : NormalizedCircle → X) (hq : Continuous q) (d : Path x (q 0)) :
    FundamentalGroup.fromPath (.mk (embeddedCircleBasedLoop (reversedEmbeddedCircle q)
      (hq.comp continuous_neg) (reversedEmbeddedCircleConnector q d))) =
      (FundamentalGroup.fromPath (.mk (embeddedCircleBasedLoop q hq d)))⁻¹ := by
  let δ := normalizedCircleStandardLoop.map hq
  have he : embeddedCircleBasedLoop (reversedEmbeddedCircle q) (hq.comp continuous_neg)
      (reversedEmbeddedCircleConnector q d) = (d.trans δ.symm).trans d.symm := by
    apply Path.ext
    funext t
    simp only [embeddedCircleBasedLoop, Path.trans_apply]
    split_ifs
    · rfl
    · change q (-normalizedCircleStandardLoop _) = q (normalizedCircleStandardLoop.symm _)
      rw [normalizedCircleStandardLoop_symm_apply]
    · rfl
  rw [he]
  change Path.Homotopic.Quotient.mk ((d.trans δ.symm).trans d.symm) =
    Path.Homotopic.Quotient.mk (((d.trans δ).trans d.symm).symm)
  rw [Path.trans_symm, Path.trans_symm, Path.symm_symm]
  exact Path.Homotopic.Quotient.trans_assoc (.mk d) (.mk δ.symm) (.mk d.symm)

/-- The actual original nonabelian marking sends the reversed once-around
embedded circle to the group inverse, without any H1 inference. -/
theorem reversedEmbeddedCircleBasedLoop_marked
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Continuous q)
    (d : Path paperGeneratorCenterPoint (q 0)) :
    modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk (embeddedCircleBasedLoop (reversedEmbeddedCircle q)
        (hq.comp continuous_neg) (reversedEmbeddedCircleConnector q d)))) =
      (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
        (FundamentalGroup.fromPath (.mk (embeddedCircleBasedLoop q hq d))))⁻¹ := by
  rw [reversedEmbeddedCircleBasedLoop_class q hq d, map_inv]

/-- Every inverse RAW signed canonical word has a literal closed embedded-circle
representative, with the exact actual original marked based class. -/
theorem quadrantPrimitiveTraceWord_inverse_has_embeddedRepresentative
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    ∃ (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
      (d : Path paperGeneratorCenterPoint (q 0)),
      modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
        (FundamentalGroup.fromPath (.mk
          ((d.trans (normalizedCircleStandardLoop.map hq.continuous)).trans d.symm))) =
          (quadrantPrimitiveTraceWord k p hp)⁻¹ := by
  obtain ⟨q, hq, d, hg⟩ := quadrantPrimitiveTraceWord_has_embeddedRepresentative k p hp
  refine ⟨reversedEmbeddedCircle q, reversedEmbeddedCircle_isClosedEmbedding hq,
    reversedEmbeddedCircleConnector q d, ?_⟩
  change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
    (FundamentalGroup.fromPath (.mk (embeddedCircleBasedLoop (reversedEmbeddedCircle q)
      (hq.continuous.comp continuous_neg) (reversedEmbeddedCircleConnector q d)))) = _
  rw [reversedEmbeddedCircleBasedLoop_marked q hq.continuous d]
  exact congrArg Inv.inv hg

end Markov
