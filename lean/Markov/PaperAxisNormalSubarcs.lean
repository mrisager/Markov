import Markov.PaperAxisCellItinerary
import Markov.PaperCellSubarc

/-! Actual Q-valued subarcs for all gaps in the constructed finite axis table.
The cell labels and containment proofs come from the actual itinerary.
Disjointness of different open subarcs is conditional on the explicitly stated
actual projected-period injectivity property; no simplicity field is added. -/

noncomputable section
open Set Topology
namespace Markov

private theorem paperAxisPeriodGap_endpoints_lt (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) :
    paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a i) <
      paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i) :=
  nonempty_Ioo.mp (paperAxisPeriodCutTable_gap_nonempty g hg a
    (paperAxisGapLeftIndex g hg a i) (paperAxisGapRightIndex g hg a i) rfl)

/-- The literal real parameter for each actual table gap. -/
def paperAxisPeriodGapParameter (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (s : unitInterval) : ℝ :=
  paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a i) +
    (paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i) -
      paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a i)) * (s:ℝ)

/-- Interior unit parameters give actual parameters strictly within their gap. -/
theorem paperAxisPeriodGapParameter_mem_gap (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1))
    (s : unitInterval) (hs0 : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1) :
    paperAxisPeriodGapParameter g hg a i s ∈
      Ioo (paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a i))
        (paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i)) := by
  have hlt := paperAxisPeriodGap_endpoints_lt g hg a i
  dsimp only [paperAxisPeriodGapParameter]
  constructor <;> nlinarith

/-- Every such parameter lies in the actual open metric period. -/
theorem paperAxisPeriodGapParameter_mem_period (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1))
    (s : unitInterval) (hs0 : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1) :
    paperAxisPeriodGapParameter g hg a i s ∈ Ioo a (a+modularClosedGeodesicPeriod g) := by
  have hgap := paperAxisPeriodGapParameter_mem_gap g hg a i s hs0 hs1
  exact ⟨lt_of_le_of_lt (paperAxisPeriodCutTable_bounds g hg a _).1 hgap.1,
    lt_of_lt_of_le hgap.2 (paperAxisPeriodCutTable_bounds g hg a _).2⟩

/-- The actual Q-valued Path for each actual finite gap, with actual pulled-back
subtype endpoints and the constructed cell label. -/
def paperAxisPeriodGapSubarc (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) :=
  paperCellSubarc (modularHyperbolicAxis g hg) (modularHyperbolicAxis_isometry g hg).continuous
    (paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a i))
    (paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i))
    (paperAxisPeriodGap_endpoints_lt g hg a i) (paperAxisPeriodGapCellLabel g hg a i)
    (paperAxisPeriodGapCellLabel_spec g hg a i).2

@[simp] theorem paperAxisPeriodGapSubarc_val (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (s : unitInterval) :
    (paperAxisPeriodGapSubarc g hg a i s : UpperHalfPlane) =
      (paperAxisPeriodGapCellLabel g hg a i)⁻¹ •
        modularHyperbolicAxis g hg (paperAxisPeriodGapParameter g hg a i s) := rfl

/-- The exact original cell action recovers the actual selected axis subarc. -/
theorem paperAxisPeriodGapSubarc_smul (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (s : unitInterval) :
    paperAxisPeriodGapCellLabel g hg a i • (paperAxisPeriodGapSubarc g hg a i s : UpperHalfPlane) =
      modularHyperbolicAxis g hg (paperAxisPeriodGapParameter g hg a i s) := by
  simp only [paperAxisPeriodGapSubarc_val, smul_inv_smul]

/-- The actual quotient projection of the normal subarc is the original curve. -/
theorem paperAxisPeriodGapSubarc_project (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (s : unitInterval) :
    modularTraceQuotientMk (paperAxisPeriodGapSubarc g hg a i s) =
      modularTraceQuotientMk (modularHyperbolicAxis g hg (paperAxisPeriodGapParameter g hg a i s)) :=
  modularTraceQuotientMk_smul (paperAxisPeriodGapCellLabel g hg a i)⁻¹ _

/-- Every open subarc point satisfies the literal strict original-Q inequalities. -/
theorem paperAxisPeriodGapSubarc_strict (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1))
    (s : unitInterval) (hs0 : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1) :
    (paperAxisPeriodGapSubarc g hg a i s : UpperHalfPlane) ∈ paperIdealQuadrilateralStrictRegion :=
  paperCellSubarc_strict_of_interior _ _ _ _ _ _ _
    (paperAxisPeriodGapCellLabel_spec g hg a i).1 s hs0 hs1

/-- In particular the open subarc lies in the actual topological interior. -/
theorem paperAxisPeriodGapSubarc_interior (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1))
    (s : unitInterval) (hs0 : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1) :
    (paperAxisPeriodGapSubarc g hg a i s : UpperHalfPlane) ∈ interior paperIdealQuadrilateral :=
  paperIdealQuadrilateralStrictRegion_subset_interior
    (paperAxisPeriodGapSubarc_strict g hg a i s hs0 hs1)

/-- Actual axis isometry proves true parameter injectivity of every normal subarc. -/
theorem paperAxisPeriodGapSubarc_injective (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) :
    Function.Injective (paperAxisPeriodGapSubarc g hg a i) :=
  paperCellSubarc_injective_of_isometry _ (modularHyperbolicAxis_isometry g hg) _ _ _ _ _

/-- Every constructed Q-valued normal subarc is an actual closed embedding. -/
theorem paperAxisPeriodGapSubarc_isClosedEmbedding (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) :
    IsClosedEmbedding (paperAxisPeriodGapSubarc g hg a i) :=
  paperCellSubarc_isClosedEmbedding_of_isometry _ (modularHyperbolicAxis_isometry g hg) _ _ _ _ _

private theorem paperAxisPeriodGapParameter_lt_of_gap_lt (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i j : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (hij : i < j)
    (s t : unitInterval) (hs0 : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1)
    (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) :
    paperAxisPeriodGapParameter g hg a i s < paperAxisPeriodGapParameter g hg a j t := by
  have hindices : paperAxisGapRightIndex g hg a i ≤ paperAxisGapLeftIndex g hg a j := by
    change i.val + 1 ≤ j.val
    change i.val < j.val at hij
    omega
  have hbetween := (paperAxisPeriodCutTable g hg a).monotone hindices
  have hs := paperAxisPeriodGapParameter_mem_gap g hg a i s hs0 hs1
  have ht := paperAxisPeriodGapParameter_mem_gap g hg a j t ht0 ht1
  exact (hs.2.trans_le hbetween).trans ht.1

/-- Interior parameters in distinct actual ordered gaps cannot be equal. -/
theorem paperAxisPeriodGapParameter_ne_of_ne_gap (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i j : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (hij : i ≠ j)
    (s t : unitInterval) (hs0 : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1)
    (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) :
    paperAxisPeriodGapParameter g hg a i s ≠ paperAxisPeriodGapParameter g hg a j t := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ne_of_lt (paperAxisPeriodGapParameter_lt_of_gap_lt g hg a i j hlt s t hs0 hs1 ht0 ht1)
  · exact (ne_of_lt (paperAxisPeriodGapParameter_lt_of_gap_lt g hg a j i hgt t s ht0 ht1 hs0 hs1)).symm

/-- Actual injectivity of the projected curve on the open metric period forces
points in different open Q-subarcs to be distinct. The injectivity hypothesis
is explicit and is not inferred from homology or a classification field. -/
theorem paperAxisPeriodGapSubarc_ne_of_projected_period_injective
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (hproject : Set.InjOn (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo a (a+modularClosedGeodesicPeriod g)))
    (i j : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (hij : i ≠ j)
    (s t : unitInterval) (hs0 : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1)
    (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) :
    paperAxisPeriodGapSubarc g hg a i s ≠ paperAxisPeriodGapSubarc g hg a j t := by
  intro heq
  have hproj := congrArg (fun z : paperIdealQuadrilateral => modularTraceQuotientMk z) heq
  simp only [paperAxisPeriodGapSubarc_project] at hproj
  have hparameter := hproject (paperAxisPeriodGapParameter_mem_period g hg a i s hs0 hs1)
    (paperAxisPeriodGapParameter_mem_period g hg a j t ht0 ht1) hproj
  exact paperAxisPeriodGapParameter_ne_of_ne_gap g hg a i j hij s t hs0 hs1 ht0 ht1 hparameter

/-- The actual open images of distinct Q-subarcs are disjoint under the stated
actual projected-period injectivity property. -/
theorem paperAxisPeriodGapSubarc_interiors_disjoint_of_projected_period_injective
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (hproject : Set.InjOn (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo a (a+modularClosedGeodesicPeriod g)))
    (i j : Fin ((paperAxisPeriodCutPoints g hg a).card - 1)) (hij : i ≠ j) :
    Disjoint ((paperAxisPeriodGapSubarc g hg a i) '' Ioo (0:unitInterval) 1)
      ((paperAxisPeriodGapSubarc g hg a j) '' Ioo (0:unitInterval) 1) := by
  apply disjoint_left.mpr
  rintro x ⟨s, hs, hsx⟩ ⟨t, ht, htx⟩
  exact paperAxisPeriodGapSubarc_ne_of_projected_period_injective g hg a hproject i j hij
    s t hs.1 hs.2 ht.1 ht.2 (hsx.trans htx.symm)

end Markov
