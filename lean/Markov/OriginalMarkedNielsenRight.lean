import Markov.OriginalMarkedNielsenAutomorphism
import Markov.OriginalMarkedTorusSymmetries
import Markov.BasedHomeomorphComposition

noncomputable section
namespace Markov

/-- The actual constant connector for the center-fixing coordinate swap. -/
def originalNielsenRightSwapConnector :
    Path paperGeneratorCenterPoint (modularCoordinateSwapHomeomorph paperGeneratorCenterPoint) :=
  (Path.refl paperGeneratorCenterPoint).cast rfl modularCoordinateSwapHomeomorph_center

/-- The actual modular homeomorphism S after L after S. -/
def originalNielsenRightHomeomorph : ModularTraceQuotient ≃ₜ ModularTraceQuotient :=
  (modularCoordinateSwapHomeomorph.trans originalNielsenHomeomorph).trans
    modularCoordinateSwapHomeomorph

/-- The actual raw connector is obtained by the checked geometric composition
law; every mapped connector and basepoint cast remains in the construction. -/
def originalNielsenRightConnectorRaw :
    Path paperGeneratorCenterPoint (originalNielsenRightHomeomorph paperGeneratorCenterPoint) :=
  basedHomeomorphCompositeConnector modularCoordinateSwapHomeomorph
    (modularCoordinateSwapHomeomorph.trans originalNielsenHomeomorph) paperGeneratorCenterPoint
    originalNielsenRightSwapConnector
    (basedHomeomorphCompositeConnector originalNielsenHomeomorph modularCoordinateSwapHomeomorph
      paperGeneratorCenterPoint originalNielsenConnectorCorrected originalNielsenRightSwapConnector)

/-- The actual based pi1 automorphism induced by S-L-S and that actual raw connector. -/
def originalNielsenRightRawFundamentalGroupEquiv :
    FundamentalGroup ModularTraceQuotient paperGeneratorCenterPoint ≃*
      FundamentalGroup ModularTraceQuotient paperGeneratorCenterPoint :=
  basedHomeomorphFundamentalGroupEquiv originalNielsenRightHomeomorph paperGeneratorCenterPoint
    originalNielsenRightConnectorRaw

/-- The actual raw based realization is exactly the composition of the actual
swap, corrected left realization and swap, on every genuine pi1 element. -/
theorem originalNielsenRightRawFundamentalGroupEquiv_comp :
    originalNielsenRightRawFundamentalGroupEquiv =
      (modularCoordinateSwapFundamentalGroupEquiv.trans originalNielsenFundamentalGroupEquiv).trans
        modularCoordinateSwapFundamentalGroupEquiv := by
  change basedHomeomorphFundamentalGroupEquiv
    ((modularCoordinateSwapHomeomorph.trans originalNielsenHomeomorph).trans modularCoordinateSwapHomeomorph)
    paperGeneratorCenterPoint _ = _
  unfold originalNielsenRightConnectorRaw
  rw [← basedHomeomorphFundamentalGroupEquiv_comp modularCoordinateSwapHomeomorph
    (modularCoordinateSwapHomeomorph.trans originalNielsenHomeomorph) paperGeneratorCenterPoint
    originalNielsenRightSwapConnector
    (basedHomeomorphCompositeConnector originalNielsenHomeomorph modularCoordinateSwapHomeomorph
      paperGeneratorCenterPoint originalNielsenConnectorCorrected originalNielsenRightSwapConnector)]
  rw [← basedHomeomorphFundamentalGroupEquiv_comp originalNielsenHomeomorph modularCoordinateSwapHomeomorph
    paperGeneratorCenterPoint originalNielsenConnectorCorrected originalNielsenRightSwapConnector]
  rfl

/-- The actual raw S-L-S automorphism expressed in the original nonabelian marking. -/
def originalNielsenRightRawMarkedEquiv : modularTraceSubgroup ≃* modularTraceSubgroup :=
  ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm.trans
    originalNielsenRightRawFundamentalGroupEquiv).trans
      (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift)

/-- The exact marked raw action is S after L after S on every subgroup element. -/
theorem originalNielsenRightRawMarkedEquiv_comp :
    originalNielsenRightRawMarkedEquiv =
      (originalCoordinateSwapMarkedEquiv.trans originalNielsenMarkedEquiv).trans
        originalCoordinateSwapMarkedEquiv := by
  apply MulEquiv.ext
  intro g
  change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
    (originalNielsenRightRawFundamentalGroupEquiv
      ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm g)) = _
  rw [originalNielsenRightRawFundamentalGroupEquiv_comp]
  simp only [originalCoordinateSwapMarkedEquiv, originalNielsenMarkedEquiv,
    MulEquiv.trans_apply, paperGeneratorCenterPoint, MulEquiv.symm_apply_apply]

/-- The raw original-marked A image is B*A, before the actual connector correction. -/
theorem originalNielsenRightRawMarkedEquiv_A :
    originalNielsenRightRawMarkedEquiv (paperTraceFreeGroupBasis 0) =
      paperTraceFreeGroupBasis 1 * paperTraceFreeGroupBasis 0 := by
  rw [originalNielsenRightRawMarkedEquiv_comp]
  change originalCoordinateSwapMarkedEquiv
    (originalNielsenMarkedEquiv (originalCoordinateSwapMarkedEquiv (paperTraceFreeGroupBasis 0))) = _
  rw [originalCoordinateSwapMarkedEquiv_A, originalNielsenMarkedEquiv_B, map_mul,
    originalCoordinateSwapMarkedEquiv_A, originalCoordinateSwapMarkedEquiv_B]

/-- The raw original-marked B image is B. -/
theorem originalNielsenRightRawMarkedEquiv_B :
    originalNielsenRightRawMarkedEquiv (paperTraceFreeGroupBasis 1) = paperTraceFreeGroupBasis 1 := by
  rw [originalNielsenRightRawMarkedEquiv_comp]
  change originalCoordinateSwapMarkedEquiv
    (originalNielsenMarkedEquiv (originalCoordinateSwapMarkedEquiv (paperTraceFreeGroupBasis 1))) = _
  rw [originalCoordinateSwapMarkedEquiv_B, originalNielsenMarkedEquiv_A,
    originalCoordinateSwapMarkedEquiv_A]

/-- Prepending the positive actual simple B loop corrects the right-move word order. -/
def originalNielsenRightConnectorCorrected :
    Path paperGeneratorCenterPoint (originalNielsenRightHomeomorph paperGeneratorCenterPoint) :=
  paperSimpleBLoop.trans originalNielsenRightConnectorRaw

/-- The corrected right move is induced by the same actual surface homeomorphism
and its explicitly corrected actual connector. -/
def originalNielsenRightFundamentalGroupEquiv :
    FundamentalGroup ModularTraceQuotient paperGeneratorCenterPoint ≃*
      FundamentalGroup ModularTraceQuotient paperGeneratorCenterPoint :=
  basedHomeomorphFundamentalGroupEquiv originalNielsenRightHomeomorph paperGeneratorCenterPoint
    originalNielsenRightConnectorCorrected

private theorem positiveConnector_conjugate {X : Type*} [TopologicalSpace X]
    (f : X ≃ₜ X) (x : X) (c : Path x (f x)) (a : Path x x)
    (g : FundamentalGroup X x) :
    basedHomeomorphFundamentalGroupEquiv f x (a.trans c) g =
      (FundamentalGroup.fromPath (.mk a))⁻¹ *
        basedHomeomorphFundamentalGroupEquiv f x c g * FundamentalGroup.fromPath (.mk a) := by
  induction g using Path.Homotopic.Quotient.ind with
  | mk γ =>
    rw [basedHomeomorphFundamentalGroupEquiv_loop, basedHomeomorphFundamentalGroupEquiv_loop]
    change Path.Homotopic.Quotient.mk _ =
      (Path.Homotopic.Quotient.mk a).trans
        ((Path.Homotopic.Quotient.mk _).trans (Path.Homotopic.Quotient.mk a.symm))
    simp only [Path.trans_symm, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.trans_assoc]

/-- The actual positive-B connector change is conjugation by B inverse in the
library fundamental group. This is proved directly from actual path quotient laws. -/
theorem originalNielsenRightFundamentalGroupEquiv_conjugate
    (g : FundamentalGroup ModularTraceQuotient paperGeneratorCenterPoint) :
    originalNielsenRightFundamentalGroupEquiv g =
      (FundamentalGroup.fromPath (.mk paperSimpleBLoop))⁻¹ *
        originalNielsenRightRawFundamentalGroupEquiv g *
          FundamentalGroup.fromPath (.mk paperSimpleBLoop) :=
  positiveConnector_conjugate originalNielsenRightHomeomorph paperGeneratorCenterPoint
    originalNielsenRightConnectorRaw paperSimpleBLoop g

/-- The actual corrected right realization in the genuine original nonabelian marking. -/
def originalNielsenRightMarkedEquiv : modularTraceSubgroup ≃* modularTraceSubgroup :=
  ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm.trans
    originalNielsenRightFundamentalGroupEquiv).trans
      (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift)

/-- Exact marked conjugation formula for the actual corrected connector. -/
theorem originalNielsenRightMarkedEquiv_conjugate (g : modularTraceSubgroup) :
    originalNielsenRightMarkedEquiv g =
      (paperTraceFreeGroupBasis 1)⁻¹ * originalNielsenRightRawMarkedEquiv g * paperTraceFreeGroupBasis 1 := by
  change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
    (originalNielsenRightFundamentalGroupEquiv
      ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm g)) = _
  rw [originalNielsenRightFundamentalGroupEquiv_conjugate, map_mul, map_mul, map_inv,
    paperSimpleBLoop_marked]
  rfl

/-- Corrected genuine original-marked A image is A*B, the exact Farey-right convention. -/
theorem originalNielsenRightMarkedEquiv_A :
    originalNielsenRightMarkedEquiv (paperTraceFreeGroupBasis 0) =
      paperTraceFreeGroupBasis 0 * paperTraceFreeGroupBasis 1 := by
  rw [originalNielsenRightMarkedEquiv_conjugate, originalNielsenRightRawMarkedEquiv_A]
  group

/-- Corrected genuine original-marked B image is B. -/
theorem originalNielsenRightMarkedEquiv_B :
    originalNielsenRightMarkedEquiv (paperTraceFreeGroupBasis 1) = paperTraceFreeGroupBasis 1 := by
  rw [originalNielsenRightMarkedEquiv_conjugate, originalNielsenRightRawMarkedEquiv_B]
  group

/-- The actual homeomorphism-and-connector automorphism is exactly the checked
algebraic Farey-right Nielsen automorphism on every actual subgroup element. -/
theorem originalNielsenRightMarkedEquiv_eq_fareyRight :
    originalNielsenRightMarkedEquiv = freeBasisFareyRightAutomorphism paperTraceFreeGroupBasis := by
  have h : originalNielsenRightMarkedEquiv.toMonoidHom =
      (freeBasisFareyRightAutomorphism paperTraceFreeGroupBasis).toMonoidHom := by
    apply paperTraceFreeGroupBasis.ext_hom
    intro i
    fin_cases i
    · change originalNielsenRightMarkedEquiv (paperTraceFreeGroupBasis 0) = _
      rw [originalNielsenRightMarkedEquiv_A]
      have he := freeBasisFareyRight_zero paperTraceFreeGroupBasis
      simpa only [freeBasisFareyRight, FreeGroupBasis.map_apply] using he.symm
    · change originalNielsenRightMarkedEquiv (paperTraceFreeGroupBasis 1) = _
      rw [originalNielsenRightMarkedEquiv_B]
      have he := freeBasisFareyRight_one paperTraceFreeGroupBasis
      simpa only [freeBasisFareyRight, FreeGroupBasis.map_apply] using he.symm
  apply MulEquiv.ext
  intro g
  exact DFunLike.congr_fun h g

end Markov
