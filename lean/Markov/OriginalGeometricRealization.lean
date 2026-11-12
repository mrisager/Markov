import Markov.OriginalMarkedTorusSymmetries
import Markov.BasedHomeomorphComposition
import Markov.OriginalMarkedNielsenAutomorphism

/-! Existential realization by actual surface homeomorphisms and actual
connecting paths. These propositions retain witnesses; no arbitrary abstract
automorphism is assumed to be geometrically realizable. -/

noncomputable section
namespace Markov

/-- The actual based-homeomorphism automorphism in the original nonabelian marking. -/
def originalMarkedHomeomorphEquiv (f : ModularTraceQuotient ≃ₜ ModularTraceQuotient)
    (c : Path paperGeneratorCenterPoint (f paperGeneratorCenterPoint)) :
    modularTraceSubgroup ≃* modularTraceSubgroup :=
  ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm.trans
    (basedHomeomorphFundamentalGroupEquiv f paperGeneratorCenterPoint c)).trans
      (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift)

/-- Actual composition, with its actual transported connector. -/
theorem originalMarkedHomeomorphEquiv_comp
    (f g : ModularTraceQuotient ≃ₜ ModularTraceQuotient)
    (cf : Path paperGeneratorCenterPoint (f paperGeneratorCenterPoint))
    (cg : Path paperGeneratorCenterPoint (g paperGeneratorCenterPoint)) :
    (originalMarkedHomeomorphEquiv g cg).trans (originalMarkedHomeomorphEquiv f cf) =
      originalMarkedHomeomorphEquiv (g.trans f)
        (basedHomeomorphCompositeConnector f g paperGeneratorCenterPoint cf cg) := by
  unfold originalMarkedHomeomorphEquiv
  rw [← basedHomeomorphFundamentalGroupEquiv_comp f g paperGeneratorCenterPoint cf cg]
  apply MulEquiv.ext
  intro a
  simp only [MulEquiv.trans_apply]
  exact congrArg
    (fun b : FundamentalGroup ModularTraceQuotient paperGeneratorCenterPoint =>
      modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
        (basedHomeomorphFundamentalGroupEquiv f paperGeneratorCenterPoint cf b))
    ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm_apply_apply
      (basedHomeomorphFundamentalGroupEquiv g paperGeneratorCenterPoint cg
        ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm a)))

/-- Actual inverse realization through the actual inverse homeomorphism and reversed mapped connector. -/
theorem originalMarkedHomeomorphEquiv_inverse
    (f : ModularTraceQuotient ≃ₜ ModularTraceQuotient)
    (c : Path paperGeneratorCenterPoint (f paperGeneratorCenterPoint)) :
    originalMarkedHomeomorphEquiv f.symm
      (basedHomeomorphInverseConnector f paperGeneratorCenterPoint c) =
        (originalMarkedHomeomorphEquiv f c).symm := by
  apply MulEquiv.ext
  intro a
  change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
    (basedHomeomorphFundamentalGroupEquiv f.symm paperGeneratorCenterPoint
      (basedHomeomorphInverseConnector f paperGeneratorCenterPoint c)
      ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm a)) = _
  rw [basedHomeomorphFundamentalGroupEquiv_inverse]
  rfl

/-- The identity surface homeomorphism and constant connector give the identity marking action. -/
theorem originalMarkedHomeomorphEquiv_refl :
    originalMarkedHomeomorphEquiv (Homeomorph.refl ModularTraceQuotient)
      (Path.refl paperGeneratorCenterPoint) = MulEquiv.refl modularTraceSubgroup := by
  apply MulEquiv.ext
  intro a
  change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
    (basedHomeomorphFundamentalGroupEquiv (Homeomorph.refl ModularTraceQuotient)
      paperGeneratorCenterPoint (Path.refl paperGeneratorCenterPoint)
      ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm a)) = a
  rw [basedHomeomorphFundamentalGroupEquiv_refl]
  exact MulEquiv.apply_symm_apply _ _

/-- An automorphism is geometrically realized precisely when actual witnesses
f and c induce it through the actual fundamental group and its proved marking. -/
def OriginalGeometricAutomorphism (e : modularTraceSubgroup ≃* modularTraceSubgroup) : Prop :=
  ∃ (f : ModularTraceQuotient ≃ₜ ModularTraceQuotient)
    (c : Path paperGeneratorCenterPoint (f paperGeneratorCenterPoint)),
      originalMarkedHomeomorphEquiv f c = e

/-- A literal ordered pair is realized by actual images of the original generators,
with an actual surface homeomorphism and actual connector as existential witnesses. -/
def OriginalPairGeometricallyRealized (g h : modularTraceSubgroup) : Prop :=
  ∃ (f : ModularTraceQuotient ≃ₜ ModularTraceQuotient)
    (c : Path paperGeneratorCenterPoint (f paperGeneratorCenterPoint)),
      originalMarkedHomeomorphEquiv f c (paperTraceFreeGroupBasis 0) = g ∧
      originalMarkedHomeomorphEquiv f c (paperTraceFreeGroupBasis 1) = h

theorem originalPairGeometricallyRealized_iff (g h : modularTraceSubgroup) :
    OriginalPairGeometricallyRealized g h ↔
      ∃ e, OriginalGeometricAutomorphism e ∧
        e (paperTraceFreeGroupBasis 0) = g ∧ e (paperTraceFreeGroupBasis 1) = h := by
  constructor
  · rintro ⟨f, c, hA, hB⟩
    exact ⟨originalMarkedHomeomorphEquiv f c, ⟨f, c, rfl⟩, hA, hB⟩
  · rintro ⟨e, ⟨f, c, rfl⟩, hA, hB⟩
    exact ⟨f, c, hA, hB⟩

/-- Identity realization uses literal identity witnesses. -/
theorem OriginalGeometricAutomorphism.refl :
    OriginalGeometricAutomorphism (MulEquiv.refl modularTraceSubgroup) :=
  ⟨Homeomorph.refl _, Path.refl _, originalMarkedHomeomorphEquiv_refl⟩

/-- Composition closure constructs the composite homeomorphism and connector. -/
theorem OriginalGeometricAutomorphism.trans
    {e d : modularTraceSubgroup ≃* modularTraceSubgroup}
    (he : OriginalGeometricAutomorphism e) (hd : OriginalGeometricAutomorphism d) :
    OriginalGeometricAutomorphism (e.trans d) := by
  rcases he with ⟨g, cg, rfl⟩
  rcases hd with ⟨f, cf, rfl⟩
  exact ⟨g.trans f, basedHomeomorphCompositeConnector f g paperGeneratorCenterPoint cf cg,
    (originalMarkedHomeomorphEquiv_comp f g cf cg).symm⟩

/-- Inverse closure constructs the actual inverse homeomorphism and connector. -/
theorem OriginalGeometricAutomorphism.symm
    {e : modularTraceSubgroup ≃* modularTraceSubgroup}
    (he : OriginalGeometricAutomorphism e) : OriginalGeometricAutomorphism e.symm := by
  rcases he with ⟨f, c, rfl⟩
  exact ⟨f.symm, basedHomeomorphInverseConnector f paperGeneratorCenterPoint c,
    originalMarkedHomeomorphEquiv_inverse f c⟩

/-- The literal original A/B pair has actual identity witnesses. -/
theorem originalPairGeometricallyRealized_basis :
    OriginalPairGeometricallyRealized (paperTraceFreeGroupBasis 0) (paperTraceFreeGroupBasis 1) := by
  apply (originalPairGeometricallyRealized_iff _ _).mpr
  exact ⟨MulEquiv.refl _, OriginalGeometricAutomorphism.refl, rfl, rfl⟩

/-- The actual coordinate swap supplies an actual realized interchange automorphism. -/
theorem originalCoordinateSwap_geometricallyRealized :
    OriginalGeometricAutomorphism originalCoordinateSwapMarkedEquiv := by
  refine ⟨modularCoordinateSwapHomeomorph,
    (Path.refl paperGeneratorCenterPoint).cast rfl modularCoordinateSwapHomeomorph_center, ?_⟩
  rfl

/-- The actual first-coordinate reflection realizes inversion of the second original generator. -/
theorem originalFirstReflection_geometricallyRealized :
    OriginalGeometricAutomorphism originalFirstReflectionMarkedEquiv := by
  refine ⟨modularFirstReflectionHomeomorph,
    (Path.refl paperGeneratorCenterPoint).cast rfl modularFirstReflectionHomeomorph_center, ?_⟩
  rfl

/-- The proved concrete corrected Nielsen homeomorphism realizes the Farey-left substitution. -/
theorem originalNielsenLeft_geometricallyRealized :
    OriginalGeometricAutomorphism originalNielsenMarkedEquiv := by
  exact ⟨originalNielsenHomeomorph, originalNielsenConnectorCorrected, rfl⟩

/-- Swapping any realized pair constructs another actually realized pair. -/
theorem OriginalPairGeometricallyRealized.swap {g h : modularTraceSubgroup}
    (hp : OriginalPairGeometricallyRealized g h) : OriginalPairGeometricallyRealized h g := by
  rcases (originalPairGeometricallyRealized_iff _ _).mp hp with ⟨e, he, hA, hB⟩
  apply (originalPairGeometricallyRealized_iff _ _).mpr
  refine ⟨originalCoordinateSwapMarkedEquiv.trans e,
    originalCoordinateSwap_geometricallyRealized.trans he, ?_, ?_⟩
  · rw [MulEquiv.trans_apply, originalCoordinateSwapMarkedEquiv_A, hB]
  · rw [MulEquiv.trans_apply, originalCoordinateSwapMarkedEquiv_B, hA]

/-- Inverting the second member uses the actual reflected circle homeomorphism. -/
theorem OriginalPairGeometricallyRealized.invert_second {g h : modularTraceSubgroup}
    (hp : OriginalPairGeometricallyRealized g h) : OriginalPairGeometricallyRealized g h⁻¹ := by
  rcases (originalPairGeometricallyRealized_iff _ _).mp hp with ⟨e, he, hA, hB⟩
  apply (originalPairGeometricallyRealized_iff _ _).mpr
  refine ⟨originalFirstReflectionMarkedEquiv.trans e,
    originalFirstReflection_geometricallyRealized.trans he, ?_, ?_⟩
  · rw [MulEquiv.trans_apply, originalFirstReflectionMarkedEquiv_A, hA]
  · rw [MulEquiv.trans_apply, originalFirstReflectionMarkedEquiv_B, map_inv, hB]

/-- Inversion of the first member is a composition of the actual swap and reflection witnesses. -/
theorem OriginalPairGeometricallyRealized.invert_first {g h : modularTraceSubgroup}
    (hp : OriginalPairGeometricallyRealized g h) : OriginalPairGeometricallyRealized g⁻¹ h :=
  hp.swap.invert_second.swap

/-- Actual left Nielsen closure, with the literal matrix/group product order retained. -/
theorem OriginalPairGeometricallyRealized.left {g h : modularTraceSubgroup}
    (hp : OriginalPairGeometricallyRealized g h) : OriginalPairGeometricallyRealized g (g*h) := by
  rcases (originalPairGeometricallyRealized_iff _ _).mp hp with ⟨e, he, hA, hB⟩
  apply (originalPairGeometricallyRealized_iff _ _).mpr
  refine ⟨originalNielsenMarkedEquiv.trans e,
    originalNielsenLeft_geometricallyRealized.trans he, ?_, ?_⟩
  · rw [MulEquiv.trans_apply, originalNielsenMarkedEquiv_A, hA]
  · rw [MulEquiv.trans_apply, originalNielsenMarkedEquiv_B, map_mul, hA, hB]

/-- Actual right Nielsen closure derived from the already constructed swap,
reflection and left witnesses; this does not assume a new realization field. -/
theorem OriginalPairGeometricallyRealized.right {g h : modularTraceSubgroup}
    (hp : OriginalPairGeometricallyRealized g h) : OriginalPairGeometricallyRealized (g*h) h := by
  have hr := hp.invert_first.invert_second.swap.left.swap.invert_first.invert_second
  simpa only [mul_inv_rev, inv_inv] using hr

end Markov
