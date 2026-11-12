import Markov.ModularTraceMonodromy
import Markov.CoveringLoopEndpoint
import Markov.PaperFreeGroup

/-! The fundamental group of the modular orbit quotient. Inversion
corrects the endpoint labelling's reversal of endomorphism multiplication.
The singular homology calculation is in `ModularTraceSingularH1`. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

def modularTraceLoopDeckEquiv (z : UpperHalfPlane) :
    Path.Homotopic.Quotient (modularTraceQuotientMk z) (modularTraceQuotientMk z) ≃
      modularTraceSubgroup :=
  (coveringLoopEndpointEquiv modularTraceQuotientMk_isCoveringMap z).trans
    (modularTraceFibreEquiv z).symm

theorem modularTraceLoopDeckEquiv_fibre (z : UpperHalfPlane)
    (c : Path.Homotopic.Quotient (modularTraceQuotientMk z) (modularTraceQuotientMk z)) :
    modularTraceFibreEquiv z (modularTraceLoopDeckEquiv z c) =
      modularTraceQuotientMk_isCoveringMap.monodromy c ⟨z, rfl⟩ :=
  (modularTraceFibreEquiv z).apply_symm_apply _

theorem modularTraceLoopDeckEquiv_trans (z : UpperHalfPlane)
    (c d : Path.Homotopic.Quotient (modularTraceQuotientMk z) (modularTraceQuotientMk z)) :
    modularTraceLoopDeckEquiv z (c.trans d) =
      modularTraceLoopDeckEquiv z c * modularTraceLoopDeckEquiv z d := by
  apply (modularTraceFibreEquiv z).injective
  rw [modularTraceLoopDeckEquiv_fibre,
    modularTraceQuotientMk_isCoveringMap.monodromy_trans_apply,
    modularTraceFibreEquiv_mul]
  have hc : modularTraceQuotientMk_isCoveringMap.monodromy c ⟨z, rfl⟩ =
      modularTraceFibreTranslate z (modularTraceLoopDeckEquiv z c) ⟨z, rfl⟩ := by
    rw [← modularTraceLoopDeckEquiv_fibre]
    rfl
  rw [hc, modularTraceMonodromy_translate, ← modularTraceLoopDeckEquiv_fibre]

/-- A genuine group equivalence for the actual surface quotient, using
inverse endpoint labels to respect `CategoryTheory.End.mul_def`. -/
def modularTraceFundamentalGroupEquiv (z : UpperHalfPlane) :
    FundamentalGroup ModularTraceQuotient (modularTraceQuotientMk z) ≃*
      modularTraceSubgroup where
  toEquiv := (modularTraceLoopDeckEquiv z).trans (Equiv.inv _)
  map_mul' c d := by
    change (modularTraceLoopDeckEquiv z (d.toPath.trans c.toPath))⁻¹ =
      (modularTraceLoopDeckEquiv z c.toPath)⁻¹ * (modularTraceLoopDeckEquiv z d.toPath)⁻¹
    rw [modularTraceLoopDeckEquiv_trans, mul_inv_rev]

@[simp] theorem modularTraceFundamentalGroupEquiv_apply (z : UpperHalfPlane)
    (c : FundamentalGroup ModularTraceQuotient (modularTraceQuotientMk z)) :
    modularTraceFundamentalGroupEquiv z c = (modularTraceLoopDeckEquiv z c.toPath)⁻¹ := rfl

/-- A path to `g⁻¹ • z` projects to the loop labelled by `g` under the
explicit inverse-endpoint convention. No choice of a surface marking is hidden. -/
def modularTraceDeckLoop (z : UpperHalfPlane) (g : modularTraceSubgroup) :
    Path (modularTraceQuotientMk z) (modularTraceQuotientMk z) :=
  ((PathConnectedSpace.somePath z (g⁻¹ • z)).map modularTraceQuotientMk_continuous).cast
    rfl (modularTraceQuotientMk_smul g⁻¹ z).symm

theorem modularTraceFundamentalGroupEquiv_deckLoop (z : UpperHalfPlane)
    (g : modularTraceSubgroup) :
    modularTraceFundamentalGroupEquiv z (.fromPath (.mk (modularTraceDeckLoop z g))) = g := by
  have he := coveringLoopEndpoint_projectedPath modularTraceQuotientMk_isCoveringMap
    (PathConnectedSpace.somePath z (g⁻¹ • z)) (modularTraceQuotientMk_smul g⁻¹ z)
  have hl : modularTraceLoopDeckEquiv z (.mk (modularTraceDeckLoop z g)) = g⁻¹ := by
    apply (modularTraceFibreEquiv z).injective
    rw [modularTraceLoopDeckEquiv_fibre]
    exact he
  change (modularTraceLoopDeckEquiv z (.mk (modularTraceDeckLoop z g)))⁻¹ = g
  rw [hl, inv_inv]

/-- The actual quotient fundamental group has a genuine rank-two free
basis, with its two represented generator loops specified below. -/
def modularTraceFundamentalGroupBasis (z : UpperHalfPlane) :
    FreeGroupBasis (Fin 2)
      (FundamentalGroup ModularTraceQuotient (modularTraceQuotientMk z)) :=
  ⟨(modularTraceFundamentalGroupEquiv z).trans paperTraceFreeGroupEquiv.symm⟩

@[simp] theorem modularTraceFundamentalGroupBasis_generator (z : UpperHalfPlane)
    (i : Fin 2) :
    modularTraceFundamentalGroupBasis z i =
      FundamentalGroup.fromPath (.mk (modularTraceDeckLoop z (paperTraceFreeGroupBasis i))) := by
  apply (modularTraceFundamentalGroupEquiv z).injective
  rw [modularTraceFundamentalGroupEquiv_deckLoop]
  change (modularTraceFundamentalGroupEquiv z)
    ((modularTraceFundamentalGroupEquiv z).symm (paperTraceFreeGroupBasis i)) =
      paperTraceFreeGroupBasis i
  exact (modularTraceFundamentalGroupEquiv z).apply_symm_apply _

end Markov
