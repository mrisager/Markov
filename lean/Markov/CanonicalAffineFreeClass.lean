import Markov.SeededLinearFareyWitnesses
import Markov.ReversedEmbeddedCircles
import Markov.CanonicalAxisMarkedClass

noncomputable section
open Topology
namespace Markov

theorem originalLinear_firstAffinePartner_det (u v : ℤ × ℤ) (hd : intDet u v = 1) :
    intDet (originalToStandardCircleLabel u) (-originalToStandardCircleLabel (u+v)) = 1 := by
  have he : intDet (originalToStandardCircleLabel u) (-originalToStandardCircleLabel (u+v)) =
      intDet u v := by simp [originalToStandardCircleLabel, intDet]; ring
  exact he.trans hd

theorem originalLinear_secondAffinePartner_det (u v : ℤ × ℤ) (hd : intDet u v = 1) :
    intDet (originalToStandardCircleLabel v) (originalToStandardCircleLabel (u+v)) = 1 := by
  have he : intDet (originalToStandardCircleLabel v) (originalToStandardCircleLabel (u+v)) =
      intDet u v := by simp [originalToStandardCircleLabel, intDet]; ring
  exact he.trans hd

/-- Reverse the actual first calibrated generator image: its direction is
literally J(u), with the constructed negative partner and actual half offset. -/
theorem OriginalPairLinearMap.first_reversed_affine
    {u v : ℤ × ℤ} {f : ModularTraceQuotient ≃ₜ ModularTraceQuotient}
    (hlin : OriginalPairLinearMap u v f) (hd : intDet u v = 1) (t : NormalizedCircle) :
    reversedEmbeddedCircle (realizedGeneratorCircle f 0) t =
      modularAffineCircle (originalToStandardCircleLabel u) (-originalToStandardCircleLabel (u+v))
        (originalLinear_firstAffinePartner_det u v hd) standardCircleHalf standardCircleHalf_ne_zero t := by
  change f (paperSimpleACircle (-(-t))) = _
  rw [neg_neg]
  apply modularTraceQuotientPuncturedTorusHomeomorph.injective
  apply Subtype.ext
  rw [hlin]
  simp only [paperSimpleACircle, modularAffineCircle, Function.comp_apply,
    Homeomorph.apply_symm_apply, standardPuncturedAffineCircle]
  have hphase : standardTorusIntegerCombination (originalToStandardCircleLabel u)
      (-originalToStandardCircleLabel (u+v)) t standardCircleHalf =
      standardTorusIntegerCombination (originalToStandardCircleLabel u)
        (originalToStandardCircleLabel (u+v)) t standardCircleHalf := by
    apply Prod.ext <;>
      simp only [standardTorusIntegerCombination, Prod.fst_neg, Prod.snd_neg,
        neg_smul, ← smul_neg, standardCircleHalf_neg]
  rw [hphase]
  have hsum : originalToStandardCircleLabel (u+v) =
      originalToStandardCircleLabel v + originalToStandardCircleLabel u := by
    ext <;> simp [originalToStandardCircleLabel, add_comm]
  rw [hsum]
  apply Prod.ext <;>
    simp only [standardTorusColumnMap, standardTorusIntegerCombination, Prod.fst_add,
      Prod.snd_add, smul_add, add_smul] <;> abel

/-- The second reversed image has direction J(v) and the positive constructed
partner, retaining its literal affine phase and offset. -/
theorem OriginalPairLinearMap.second_reversed_affine
    {u v : ℤ × ℤ} {f : ModularTraceQuotient ≃ₜ ModularTraceQuotient}
    (hlin : OriginalPairLinearMap u v f) (hd : intDet u v = 1) (t : NormalizedCircle) :
    reversedEmbeddedCircle (realizedGeneratorCircle f 1) t =
      modularAffineCircle (originalToStandardCircleLabel v) (originalToStandardCircleLabel (u+v))
        (originalLinear_secondAffinePartner_det u v hd) standardCircleHalf standardCircleHalf_ne_zero t := by
  change f (paperSimpleBCircle (-(-t))) = _
  rw [neg_neg]
  apply modularTraceQuotientPuncturedTorusHomeomorph.injective
  apply Subtype.ext
  rw [hlin]
  simp only [paperSimpleBCircle, modularAffineCircle, Function.comp_apply,
    Homeomorph.apply_symm_apply, standardPuncturedAffineCircle]
  have hsum : originalToStandardCircleLabel (u+v) =
      originalToStandardCircleLabel v + originalToStandardCircleLabel u := by
    ext <;> simp [originalToStandardCircleLabel, add_comm]
  rw [hsum]
  apply Prod.ext <;>
    simp only [standardTorusColumnMap, standardTorusIntegerCombination, Prod.fst_add,
      Prod.snd_add, smul_add, add_smul] <;> abel

/-- A proved literal affine image transports the actual reversed generator's
full nonabelian class, with its actual connector retained. -/
theorem realizedGenerator_reversed_affine_marked
    (f : ModularTraceQuotient ≃ₜ ModularTraceQuotient)
    (c : Path paperGeneratorCenterPoint (f paperGeneratorCenterPoint)) (i : Fin 2)
    (p q : ℤ × ℤ) (hpq : intDet p q = 1)
    (heq : ∀ t, reversedEmbeddedCircle (realizedGeneratorCircle f i) t =
      modularAffineCircle p q hpq standardCircleHalf standardCircleHalf_ne_zero t) :
    ∃ d : Path paperGeneratorCenterPoint
        (modularAffineCircle p q hpq standardCircleHalf standardCircleHalf_ne_zero 0),
      modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
        (FundamentalGroup.fromPath (.mk
          ((d.trans (modularAffineCircleLoop p q hpq standardCircleHalf standardCircleHalf_ne_zero)).trans d.symm))) =
        (originalMarkedHomeomorphEquiv f c (paperTraceFreeGroupBasis i))⁻¹ := by
  let q0 := realizedGeneratorCircle f i
  let hq0 := realizedGeneratorCircle_isClosedEmbedding f i
  let d0 := realizedGeneratorCircleConnector f c i
  have hm : modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk (embeddedCircleBasedLoop (reversedEmbeddedCircle q0)
        (hq0.continuous.comp continuous_neg) (reversedEmbeddedCircleConnector q0 d0)))) =
      (originalMarkedHomeomorphEquiv f c (paperTraceFreeGroupBasis i))⁻¹ := by
    exact (reversedEmbeddedCircleBasedLoop_marked q0 hq0.continuous d0).trans
      (congrArg Inv.inv (realizedGeneratorCircleBasedLoop_marked f c i))
  have hf : reversedEmbeddedCircle q0 =
      modularAffineCircle p q hpq standardCircleHalf standardCircleHalf_ne_zero := funext heq
  have pack : ∃ (qr : NormalizedCircle → ModularTraceQuotient) (hqr : Continuous qr)
      (d : Path paperGeneratorCenterPoint (qr 0)),
      qr = modularAffineCircle p q hpq standardCircleHalf standardCircleHalf_ne_zero ∧
      modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
        (FundamentalGroup.fromPath (.mk (embeddedCircleBasedLoop qr hqr d))) =
        (originalMarkedHomeomorphEquiv f c (paperTraceFreeGroupBasis i))⁻¹ :=
    ⟨reversedEmbeddedCircle q0, hq0.continuous.comp continuous_neg,
      reversedEmbeddedCircleConnector q0 d0, hf, hm⟩
  rcases pack with ⟨qr, hqr, d, rfl, hmark⟩
  exact ⟨d, hmark⟩

/-- The canonical forward free class has an ACTUAL affine representative
with original label p: standard direction J(p), constructed determinant-one
partner, literal half offset and exact full marked raw-word-inverse class. -/
theorem quadrantPrimitiveTraceWord_inverse_has_affineRepresentative
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    ∃ a : ℤ × ℤ, ∃ ha : intDet (originalToStandardCircleLabel p) a = 1,
      ∃ d : Path paperGeneratorCenterPoint
        (modularAffineCircle (originalToStandardCircleLabel p) a ha
          standardCircleHalf standardCircleHalf_ne_zero 0),
      modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
        (FundamentalGroup.fromPath (.mk
          ((d.trans (modularAffineCircleLoop (originalToStandardCircleLabel p) a ha
            standardCircleHalf standardCircleHalf_ne_zero)).trans d.symm))) =
          (quadrantPrimitiveTraceWord k p hp)⁻¹ := by
  obtain ⟨u, v, g, h, hd, ⟨_, f, c, hlin, hA, hB⟩, hlabel⟩ :=
    quadrantPrimitiveTraceWord_linear_pair k p hp
  rcases hlabel with ⟨rfl, hg⟩ | ⟨rfl, hh⟩
  · obtain ⟨d, hm⟩ := realizedGenerator_reversed_affine_marked f c 0
      (originalToStandardCircleLabel u) (-originalToStandardCircleLabel (u+v))
      (originalLinear_firstAffinePartner_det u v hd) (hlin.first_reversed_affine hd)
    rw [hA, hg] at hm
    exact ⟨_, originalLinear_firstAffinePartner_det u v hd, d, hm⟩
  · obtain ⟨d, hm⟩ := realizedGenerator_reversed_affine_marked f c 1
      (originalToStandardCircleLabel v) (originalToStandardCircleLabel (u+v))
      (originalLinear_secondAffinePartner_det u v hd) (hlin.second_reversed_affine hd)
    rw [hB, hh] at hm
    exact ⟨_, originalLinear_secondAffinePartner_det u v hd, d, hm⟩

/-- Actual based homotopy from the transported canonical forward geodesic
loop to the literal affine representative with the same original label p. -/
theorem paperPrimitiveAxisTransportLoop_has_affineRepresentative
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    ∃ a : ℤ × ℤ, ∃ ha : intDet (originalToStandardCircleLabel p) a = 1,
      ∃ d : Path paperGeneratorCenterPoint
        (modularAffineCircle (originalToStandardCircleLabel p) a ha
          standardCircleHalf standardCircleHalf_ne_zero 0),
      (paperPrimitiveAxisTransportLoop k p hp).Homotopic
        ((d.trans (modularAffineCircleLoop (originalToStandardCircleLabel p) a ha
          standardCircleHalf standardCircleHalf_ne_zero)).trans d.symm) := by
  obtain ⟨a, ha, d, hm⟩ := quadrantPrimitiveTraceWord_inverse_has_affineRepresentative k p hp
  refine ⟨a, ha, d, ?_⟩
  have he : FundamentalGroup.fromPath (.mk (paperPrimitiveAxisTransportLoop k p hp)) =
      FundamentalGroup.fromPath (.mk
        ((d.trans (modularAffineCircleLoop (originalToStandardCircleLabel p) a ha
          standardCircleHalf standardCircleHalf_ne_zero)).trans d.symm)) :=
    (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).injective
      ((paperPrimitiveAxisTransportLoop_marked k p hp).trans hm.symm)
  exact Path.Homotopic.Quotient.eq.mp he

end Markov
