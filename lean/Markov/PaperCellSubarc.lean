import Markov.PaperQuadrilateralFrontierCuts
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Hausdorff

/-! Literal pullbacks of continuous real subarcs into the actual original
closed quadrilateral. The source interval and the actual cell label are
explicit. Injectivity is derived from an actual isometry, not supplied. -/

noncomputable section
open Set Topology
namespace Markov

/-- Pull back an actual point in a translated closed cell to its literal
original-cell representative. -/
def paperCellPullbackPoint (F : ℝ → UpperHalfPlane) (a b : ℝ)
    (δ : modularTraceSubgroup)
    (hcell : ∀ t ∈ Icc a b,
      F t ∈ (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral)
    (t : ℝ) (ht : t ∈ Icc a b) : paperIdealQuadrilateral :=
  ⟨δ⁻¹ • F t, by
    obtain ⟨z, hz, heq⟩ := hcell t ht
    simpa only [← heq, inv_smul_smul] using hz⟩

private theorem paperCellSubarc_parameter_mem (a b : ℝ) (hab : a ≤ b)
    (s : unitInterval) : a + (b-a)*(s:ℝ) ∈ Icc a b := by
  obtain ⟨hs0, hs1⟩ := s.property
  constructor <;> nlinarith

/-- The actual path in the original closed quadrilateral has literal value
δ⁻¹•F(a+(b-a)s). Its subtype endpoints are the actual pulled-back endpoint
values, with membership proved from the supplied closed-cell containment. -/
def paperCellSubarc (F : ℝ → UpperHalfPlane) (hF : Continuous F)
    (a b : ℝ) (hab : a < b) (δ : modularTraceSubgroup)
    (hcell : ∀ t ∈ Icc a b,
      F t ∈ (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral) :
    Path (paperCellPullbackPoint F a b δ hcell a ⟨le_rfl, hab.le⟩)
      (paperCellPullbackPoint F a b δ hcell b ⟨hab.le, le_rfl⟩) where
  toFun s := paperCellPullbackPoint F a b δ hcell (a+(b-a)*(s:ℝ))
    (paperCellSubarc_parameter_mem a b hab.le s)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (modularTraceSubgroup_isometry δ⁻¹).continuous.comp
      (hF.comp (by fun_prop))
  source' := by
    apply Subtype.ext
    simp [paperCellPullbackPoint]
  target' := by
    apply Subtype.ext
    simp [paperCellPullbackPoint]

/-- The subtype value is the literal inverse-deck pullback. -/
@[simp] theorem paperCellSubarc_val (F : ℝ → UpperHalfPlane) (hF : Continuous F)
    (a b : ℝ) (hab : a < b) (δ : modularTraceSubgroup)
    (hcell : ∀ t ∈ Icc a b,
      F t ∈ (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral)
    (s : unitInterval) :
    (paperCellSubarc F hF a b hab δ hcell s : UpperHalfPlane) =
      δ⁻¹ • F (a+(b-a)*(s:ℝ)) := rfl

/-- Acting by the actual cell label recovers the original subarc pointwise. -/
theorem paperCellSubarc_smul (F : ℝ → UpperHalfPlane) (hF : Continuous F)
    (a b : ℝ) (hab : a < b) (δ : modularTraceSubgroup)
    (hcell : ∀ t ∈ Icc a b,
      F t ∈ (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral)
    (s : unitInterval) :
    δ • (paperCellSubarc F hF a b hab δ hcell s : UpperHalfPlane) =
      F (a+(b-a)*(s:ℝ)) := by
  simp only [paperCellSubarc_val, smul_inv_smul]

/-- The actual orbit projection is unchanged by this pullback. -/
theorem paperCellSubarc_project (F : ℝ → UpperHalfPlane) (hF : Continuous F)
    (a b : ℝ) (hab : a < b) (δ : modularTraceSubgroup)
    (hcell : ∀ t ∈ Icc a b,
      F t ∈ (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral)
    (s : unitInterval) :
    modularTraceQuotientMk (paperCellSubarc F hF a b hab δ hcell s) =
      modularTraceQuotientMk (F (a+(b-a)*(s:ℝ))) := by
  exact modularTraceQuotientMk_smul δ⁻¹ _

/-- Strict containment on the open real interval gives strict original-cell
interior inequalities throughout the open parameter interval of the path. -/
theorem paperCellSubarc_strict_of_interior
    (F : ℝ → UpperHalfPlane) (hF : Continuous F)
    (a b : ℝ) (hab : a < b) (δ : modularTraceSubgroup)
    (hcell : ∀ t ∈ Icc a b,
      F t ∈ (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral)
    (hstrict : ∀ t ∈ Ioo a b,
      F t ∈ (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateralStrictRegion)
    (s : unitInterval) (hs0 : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1) :
    (paperCellSubarc F hF a b hab δ hcell s : UpperHalfPlane) ∈
      paperIdealQuadrilateralStrictRegion := by
  have ht : a+(b-a)*(s:ℝ) ∈ Ioo a b := by constructor <;> nlinarith
  obtain ⟨z, hz, heq⟩ := hstrict _ ht
  simpa only [paperCellSubarc_val, ← heq, inv_smul_smul] using hz

/-- Actual topological interior containment on the open real interval is
preserved by the literal inverse-deck subarc construction. -/
theorem paperCellSubarc_interior_of_interior
    (F : ℝ → UpperHalfPlane) (hF : Continuous F)
    (a b : ℝ) (hab : a < b) (δ : modularTraceSubgroup)
    (hcell : ∀ t ∈ Icc a b,
      F t ∈ (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral)
    (hinterior : ∀ t ∈ Ioo a b,
      F t ∈ (fun z : UpperHalfPlane => δ • z) '' interior paperIdealQuadrilateral)
    (s : unitInterval) (hs0 : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1) :
    (paperCellSubarc F hF a b hab δ hcell s : UpperHalfPlane) ∈
      interior paperIdealQuadrilateral := by
  have ht : a+(b-a)*(s:ℝ) ∈ Ioo a b := by constructor <;> nlinarith
  obtain ⟨z, hz, heq⟩ := hinterior _ ht
  simpa only [paperCellSubarc_val, ← heq, inv_smul_smul] using hz

/-- An actual source isometry and a positive interval length force the
constructed path to be injective in its actual unit-interval parameter. -/
theorem paperCellSubarc_injective_of_isometry
    (F : ℝ → UpperHalfPlane) (hF : Isometry F)
    (a b : ℝ) (hab : a < b) (δ : modularTraceSubgroup)
    (hcell : ∀ t ∈ Icc a b,
      F t ∈ (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral) :
    Function.Injective (paperCellSubarc F hF.continuous a b hab δ hcell) := by
  intro s t heq
  have hvalues := congrArg (fun z : paperIdealQuadrilateral => δ • (z:UpperHalfPlane)) heq
  simp only [paperCellSubarc_smul] at hvalues
  have hparameter := hF.injective hvalues
  apply Subtype.ext
  change (s:ℝ) = (t:ℝ)
  nlinarith

/-- Compactness of the actual unit interval upgrades the derived injectivity
to an actual closed embedding into the original closed-cell subtype. -/
theorem paperCellSubarc_isClosedEmbedding_of_isometry
    (F : ℝ → UpperHalfPlane) (hF : Isometry F)
    (a b : ℝ) (hab : a < b) (δ : modularTraceSubgroup)
    (hcell : ∀ t ∈ Icc a b,
      F t ∈ (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral) :
    IsClosedEmbedding (paperCellSubarc F hF.continuous a b hab δ hcell) :=
  (paperCellSubarc F hF.continuous a b hab δ hcell).continuous.isClosedEmbedding
    (paperCellSubarc_injective_of_isometry F hF a b hab δ hcell)

end Markov
