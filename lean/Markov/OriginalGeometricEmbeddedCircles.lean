import Markov.OriginalGeometricRealization

noncomputable section
open Topology
namespace Markov

/-- The original simple generator circle with reversed circle parameter, so
its positive standard once-around loop has the calibrated original orientation. -/
def originalSimpleGeneratorCircle (i : Fin 2) (u : NormalizedCircle) : ModularTraceQuotient :=
  if i = 0 then paperSimpleACircle (-u) else paperSimpleBCircle (-u)

/-- These are actual closed circle embeddings, with the orientation reversal included. -/
theorem originalSimpleGeneratorCircle_isClosedEmbedding (i : Fin 2) :
    IsClosedEmbedding (originalSimpleGeneratorCircle i) := by
  fin_cases i
  · change IsClosedEmbedding (fun u : NormalizedCircle => paperSimpleACircle (-u))
    apply (continuous_paperSimpleACircle.comp continuous_neg).isClosedEmbedding
    intro u v h
    exact neg_injective (paperSimpleACircle_isClosedEmbedding.injective h)
  · change IsClosedEmbedding (fun u : NormalizedCircle => paperSimpleBCircle (-u))
    apply (continuous_paperSimpleBCircle.comp continuous_neg).isClosedEmbedding
    intro u v h
    exact neg_injective (paperSimpleBCircle_isClosedEmbedding.injective h)

theorem originalSimpleGeneratorCircle_zero (i : Fin 2) :
    originalSimpleGeneratorCircle i 0 = paperGeneratorCenterPoint := by
  fin_cases i
  · change paperSimpleACircle (-0) = _
    rw [neg_zero, paperSimpleACircle_zero]
  · change paperSimpleBCircle (-0) = _
    rw [neg_zero, paperSimpleBCircle_zero]

/-- The actual positive standard once-around loop of the oriented original circle. -/
def originalSimpleGeneratorLoop (i : Fin 2) : Path paperGeneratorCenterPoint paperGeneratorCenterPoint :=
  (normalizedCircleStandardLoop.map (originalSimpleGeneratorCircle_isClosedEmbedding i).continuous).cast
    (originalSimpleGeneratorCircle_zero i).symm (originalSimpleGeneratorCircle_zero i).symm

/-- The positive standard parameter on the reversed A circle is literally the calibrated A loop. -/
theorem originalSimpleGeneratorLoop_zero : originalSimpleGeneratorLoop 0 = paperSimpleALoop := by
  ext t
  change paperSimpleACircle (-(normalizedCircleStandardLoop t)) =
    paperSimpleACircle (normalizedCircleIntegerLoop (-1) t)
  rw [normalizedCircleStandardLoop_apply, normalizedCircleIntegerLoop_apply]
  simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one, AddCircle.coe_neg]

/-- The same exact orientation identity for the calibrated B loop. -/
theorem originalSimpleGeneratorLoop_one : originalSimpleGeneratorLoop 1 = paperSimpleBLoop := by
  ext t
  change paperSimpleBCircle (-(normalizedCircleStandardLoop t)) =
    paperSimpleBCircle (normalizedCircleIntegerLoop (-1) t)
  rw [normalizedCircleStandardLoop_apply, normalizedCircleIntegerLoop_apply]
  simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one, AddCircle.coe_neg]

/-- Genuine original marked nonabelian value of each oriented embedded generator. -/
theorem originalSimpleGeneratorLoop_marked (i : Fin 2) :
    modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk (originalSimpleGeneratorLoop i))) = paperTraceFreeGroupBasis i := by
  fin_cases i
  · change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk (originalSimpleGeneratorLoop 0))) = paperTraceFreeGroupBasis 0
    rw [originalSimpleGeneratorLoop_zero, paperSimpleALoop_marked]
  · change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk (originalSimpleGeneratorLoop 1))) = paperTraceFreeGroupBasis 1
    rw [originalSimpleGeneratorLoop_one, paperSimpleBLoop_marked]

/-- The literal embedded generator image under the actual witness homeomorphism. -/
def realizedGeneratorCircle (f : ModularTraceQuotient ≃ₜ ModularTraceQuotient)
    (i : Fin 2) (u : NormalizedCircle) : ModularTraceQuotient :=
  f (originalSimpleGeneratorCircle i u)

theorem realizedGeneratorCircle_isClosedEmbedding
    (f : ModularTraceQuotient ≃ₜ ModularTraceQuotient) (i : Fin 2) :
    IsClosedEmbedding (realizedGeneratorCircle f i) :=
  f.isClosedEmbedding.comp (originalSimpleGeneratorCircle_isClosedEmbedding i)

theorem realizedGeneratorCircle_zero
    (f : ModularTraceQuotient ≃ₜ ModularTraceQuotient) (i : Fin 2) :
    realizedGeneratorCircle f i 0 = f paperGeneratorCenterPoint :=
  congrArg f (originalSimpleGeneratorCircle_zero i)

/-- The actual witness connector, with only its endpoint displayed at the actual circle basepoint. -/
def realizedGeneratorCircleConnector
    (f : ModularTraceQuotient ≃ₜ ModularTraceQuotient)
    (c : Path paperGeneratorCenterPoint (f paperGeneratorCenterPoint)) (i : Fin 2) :
    Path paperGeneratorCenterPoint (realizedGeneratorCircle f i 0) :=
  c.cast rfl (realizedGeneratorCircle_zero f i)

/-- The actual conjugate of the positive once-around embedded-circle loop. -/
def realizedGeneratorCircleBasedLoop
    (f : ModularTraceQuotient ≃ₜ ModularTraceQuotient)
    (c : Path paperGeneratorCenterPoint (f paperGeneratorCenterPoint)) (i : Fin 2) :
    Path paperGeneratorCenterPoint paperGeneratorCenterPoint :=
  ((realizedGeneratorCircleConnector f c i).trans
    (normalizedCircleStandardLoop.map (realizedGeneratorCircle_isClosedEmbedding f i).continuous)).trans
      (realizedGeneratorCircleConnector f c i).symm

/-- Exact actual path equality with the witness homeomorphism's based image of
the calibrated generator; circle orientation and all casts are retained. -/
theorem realizedGeneratorCircleBasedLoop_eq
    (f : ModularTraceQuotient ≃ₜ ModularTraceQuotient)
    (c : Path paperGeneratorCenterPoint (f paperGeneratorCenterPoint)) (i : Fin 2) :
    realizedGeneratorCircleBasedLoop f c i =
      (c.trans ((originalSimpleGeneratorLoop i).map f.continuous)).trans c.symm := by
  ext t
  simp only [realizedGeneratorCircleBasedLoop, realizedGeneratorCircleConnector,
    originalSimpleGeneratorLoop, Path.cast_coe, Path.map_coe, Function.comp_apply,
    Path.trans_apply, Path.symm_apply]
  split_ifs <;> rfl

/-- Exact nonabelian marked class of the literal embedded-circle representative. -/
theorem realizedGeneratorCircleBasedLoop_marked
    (f : ModularTraceQuotient ≃ₜ ModularTraceQuotient)
    (c : Path paperGeneratorCenterPoint (f paperGeneratorCenterPoint)) (i : Fin 2) :
    modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (FundamentalGroup.fromPath (.mk (realizedGeneratorCircleBasedLoop f c i))) =
        originalMarkedHomeomorphEquiv f c (paperTraceFreeGroupBasis i) := by
  rw [realizedGeneratorCircleBasedLoop_eq, ← basedHomeomorphFundamentalGroupEquiv_loop]
  change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
    (basedHomeomorphFundamentalGroupEquiv f paperGeneratorCenterPoint c
      (FundamentalGroup.fromPath (.mk (originalSimpleGeneratorLoop i)))) =
    modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
      (basedHomeomorphFundamentalGroupEquiv f paperGeneratorCenterPoint c
        ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm
          (paperTraceFreeGroupBasis i)))
  have hs : (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm
      (paperTraceFreeGroupBasis i) = FundamentalGroup.fromPath (.mk (originalSimpleGeneratorLoop i)) := by
    apply (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).injective
    rw [MulEquiv.apply_symm_apply, originalSimpleGeneratorLoop_marked]
  rw [hs]

/-- Every actual homeomorphism-and-connector generator witness supplies a
literal closed embedded circle and an actual connector whose positive standard
once-around conjugate has exactly its prescribed original nonabelian value. -/
theorem originalMarkedHomeomorph_generator_has_embeddedRepresentative
    (f : ModularTraceQuotient ≃ₜ ModularTraceQuotient)
    (c : Path paperGeneratorCenterPoint (f paperGeneratorCenterPoint)) (i : Fin 2) :
    ∃ (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
      (d : Path paperGeneratorCenterPoint (q 0)),
      modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
        (FundamentalGroup.fromPath (.mk
          ((d.trans (normalizedCircleStandardLoop.map hq.continuous)).trans d.symm))) =
        originalMarkedHomeomorphEquiv f c (paperTraceFreeGroupBasis i) := by
  exact ⟨realizedGeneratorCircle f i, realizedGeneratorCircle_isClosedEmbedding f i,
    realizedGeneratorCircleConnector f c i, realizedGeneratorCircleBasedLoop_marked f c i⟩

/-- The same literal embedded representative for any genuinely realized automorphism generator. -/
theorem OriginalGeometricAutomorphism.generator_has_embeddedRepresentative
    {e : modularTraceSubgroup ≃* modularTraceSubgroup} (he : OriginalGeometricAutomorphism e) (i : Fin 2) :
    ∃ (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
      (d : Path paperGeneratorCenterPoint (q 0)),
      modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
        (FundamentalGroup.fromPath (.mk
          ((d.trans (normalizedCircleStandardLoop.map hq.continuous)).trans d.symm))) =
        e (paperTraceFreeGroupBasis i) := by
  rcases he with ⟨f, c, rfl⟩
  exact originalMarkedHomeomorph_generator_has_embeddedRepresentative f c i

/-- The first member of every actually realized pair has an exact nonabelian embedded representative. -/
theorem OriginalPairGeometricallyRealized.left_has_embeddedRepresentative
    {g h : modularTraceSubgroup} (hp : OriginalPairGeometricallyRealized g h) :
    ∃ (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
      (d : Path paperGeneratorCenterPoint (q 0)),
      modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
        (FundamentalGroup.fromPath (.mk
          ((d.trans (normalizedCircleStandardLoop.map hq.continuous)).trans d.symm))) = g := by
  rcases hp with ⟨f, c, hA, _⟩
  obtain ⟨q, hq, d, he⟩ := originalMarkedHomeomorph_generator_has_embeddedRepresentative f c 0
  exact ⟨q, hq, d, he.trans hA⟩

/-- The second member has the same kind of literal representative, with its actual connector retained. -/
theorem OriginalPairGeometricallyRealized.right_has_embeddedRepresentative
    {g h : modularTraceSubgroup} (hp : OriginalPairGeometricallyRealized g h) :
    ∃ (q : NormalizedCircle → ModularTraceQuotient) (hq : IsClosedEmbedding q)
      (d : Path paperGeneratorCenterPoint (q 0)),
      modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
        (FundamentalGroup.fromPath (.mk
          ((d.trans (normalizedCircleStandardLoop.map hq.continuous)).trans d.symm))) = h := by
  rcases hp with ⟨f, c, _, hB⟩
  obtain ⟨q, hq, d, he⟩ := originalMarkedHomeomorph_generator_has_embeddedRepresentative f c 1
  exact ⟨q, hq, d, he.trans hB⟩

end Markov
