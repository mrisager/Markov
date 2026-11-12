import Markov.OriginalMarkedNielsenLoops
import Markov.BasedHomeomorphFundamentalGroup
import Markov.FreeBasisFareyMoves

noncomputable section
namespace Markov

/-- The actual based pi1 automorphism induced by the actual modular shear
homeomorphism and its uncorrected transported connector. -/
def originalNielsenRawFundamentalGroupEquiv :
    FundamentalGroup ModularTraceQuotient paperGeneratorCenterPoint ≃*
      FundamentalGroup ModularTraceQuotient paperGeneratorCenterPoint :=
  basedHomeomorphFundamentalGroupEquiv originalNielsenHomeomorph paperGeneratorCenterPoint
    originalNielsenConnector

/-- The actual based pi1 automorphism induced by the same genuine homeomorphism
and the corrected explicit connector. -/
def originalNielsenFundamentalGroupEquiv :
    FundamentalGroup ModularTraceQuotient paperGeneratorCenterPoint ≃*
      FundamentalGroup ModularTraceQuotient paperGeneratorCenterPoint :=
  basedHomeomorphFundamentalGroupEquiv originalNielsenHomeomorph paperGeneratorCenterPoint
    originalNielsenConnectorCorrected

/-- Exact actual loop representative of the raw based automorphism. -/
theorem originalNielsenRawFundamentalGroupEquiv_loop
    (γ : Path paperGeneratorCenterPoint paperGeneratorCenterPoint) :
    originalNielsenRawFundamentalGroupEquiv (FundamentalGroup.fromPath (.mk γ)) =
      FundamentalGroup.fromPath (.mk (originalNielsenRawLoop γ)) :=
  basedHomeomorphFundamentalGroupEquiv_loop originalNielsenHomeomorph paperGeneratorCenterPoint
    originalNielsenConnector γ

/-- Exact actual loop representative of the corrected based automorphism. -/
theorem originalNielsenFundamentalGroupEquiv_loop
    (γ : Path paperGeneratorCenterPoint paperGeneratorCenterPoint) :
    originalNielsenFundamentalGroupEquiv (FundamentalGroup.fromPath (.mk γ)) =
      FundamentalGroup.fromPath (.mk (originalNielsenCorrectedLoop γ)) :=
  basedHomeomorphFundamentalGroupEquiv_loop originalNielsenHomeomorph paperGeneratorCenterPoint
    originalNielsenConnectorCorrected γ

/-- The actual raw induced automorphism in the original nonabelian marking. -/
def originalNielsenRawMarkedEquiv : modularTraceSubgroup ≃* modularTraceSubgroup :=
  ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm.trans
    originalNielsenRawFundamentalGroupEquiv).trans
      (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift)

/-- The actual corrected induced automorphism in the original nonabelian marking. -/
def originalNielsenMarkedEquiv : modularTraceSubgroup ≃* modularTraceSubgroup :=
  ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm.trans
    originalNielsenFundamentalGroupEquiv).trans
      (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift)

private theorem marked_symm_A :
    (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm (paperTraceFreeGroupBasis 0) =
      FundamentalGroup.fromPath (.mk paperSimpleALoop) := by
  apply (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).injective
  rw [MulEquiv.apply_symm_apply, paperSimpleALoop_marked]

private theorem marked_symm_B :
    (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm (paperTraceFreeGroupBasis 1) =
      FundamentalGroup.fromPath (.mk paperSimpleBLoop) := by
  apply (modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).injective
  rw [MulEquiv.apply_symm_apply, paperSimpleBLoop_marked]

/-- Exact raw original marked A image. -/
theorem originalNielsenRawMarkedEquiv_A :
    originalNielsenRawMarkedEquiv (paperTraceFreeGroupBasis 0) = paperTraceFreeGroupBasis 0 := by
  change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
    (originalNielsenRawFundamentalGroupEquiv
      ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm (paperTraceFreeGroupBasis 0))) = _
  rw [marked_symm_A, originalNielsenRawFundamentalGroupEquiv_loop, originalNielsenRawLoop_A_marked]

/-- Exact raw original marked B image is B*A. -/
theorem originalNielsenRawMarkedEquiv_B :
    originalNielsenRawMarkedEquiv (paperTraceFreeGroupBasis 1) =
      paperTraceFreeGroupBasis 1 * paperTraceFreeGroupBasis 0 := by
  change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
    (originalNielsenRawFundamentalGroupEquiv
      ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm (paperTraceFreeGroupBasis 1))) = _
  rw [marked_symm_B, originalNielsenRawFundamentalGroupEquiv_loop, originalNielsenRawLoop_B_marked]

/-- The actual corrected original marked automorphism fixes A. -/
theorem originalNielsenMarkedEquiv_A :
    originalNielsenMarkedEquiv (paperTraceFreeGroupBasis 0) = paperTraceFreeGroupBasis 0 := by
  change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
    (originalNielsenFundamentalGroupEquiv
      ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm (paperTraceFreeGroupBasis 0))) = _
  rw [marked_symm_A, originalNielsenFundamentalGroupEquiv_loop, originalNielsenCorrectedLoop_A_marked]

/-- Its actual corrected original marked B image is A*B. -/
theorem originalNielsenMarkedEquiv_B :
    originalNielsenMarkedEquiv (paperTraceFreeGroupBasis 1) =
      paperTraceFreeGroupBasis 0 * paperTraceFreeGroupBasis 1 := by
  change modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift
    (originalNielsenFundamentalGroupEquiv
      ((modularTraceMarkedFundamentalGroupEquiv paperGeneratorCenterLift).symm (paperTraceFreeGroupBasis 1))) = _
  rw [marked_symm_B, originalNielsenFundamentalGroupEquiv_loop, originalNielsenCorrectedLoop_B_marked]

/-- The actual homeomorphism-and-connector pi1 automorphism is exactly the
previously checked algebraic Farey left Nielsen automorphism, on every group element.
The equality uses the genuine original free basis and proved nonabelian generator images. -/
theorem originalNielsenMarkedEquiv_eq_fareyLeft :
    originalNielsenMarkedEquiv = freeBasisFareyLeftAutomorphism paperTraceFreeGroupBasis := by
  have h : originalNielsenMarkedEquiv.toMonoidHom =
      (freeBasisFareyLeftAutomorphism paperTraceFreeGroupBasis).toMonoidHom := by
    apply paperTraceFreeGroupBasis.ext_hom
    intro i
    fin_cases i
    · change originalNielsenMarkedEquiv (paperTraceFreeGroupBasis 0) = _
      rw [originalNielsenMarkedEquiv_A]
      have he := freeBasisFareyLeft_zero paperTraceFreeGroupBasis
      simpa only [freeBasisFareyLeft, FreeGroupBasis.map_apply] using he.symm
    · change originalNielsenMarkedEquiv (paperTraceFreeGroupBasis 1) = _
      rw [originalNielsenMarkedEquiv_B]
      have he := freeBasisFareyLeft_one paperTraceFreeGroupBasis
      simpa only [freeBasisFareyLeft, FreeGroupBasis.map_apply] using he.symm
  apply MulEquiv.ext
  intro g
  exact DFunLike.congr_fun h g

end Markov
