import Markov.PaperAxisWrapSubarc
import Markov.PaperAxisOrderedCellWord

/-! The actual finite proper original-Q arc family consists of ONE joined
wrap arc, indexed by zero, and precisely the internal table gaps, indexed by
1 through card(cutPoints)-3. No endpoint order or diagram classification is
assumed. -/
noncomputable section
open Set Topology
namespace Markov

/-- The literal finite index type: one wrap member and every internal gap. -/
abbrev paperAxisProperArcIndex (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :=
  Fin ((paperAxisPeriodCutPoints g hg a).card - 2)

private def properArcGapIndex (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : paperAxisProperArcIndex g hg a) :
    Fin ((paperAxisPeriodCutPoints g hg a).card - 1) :=
  ⟨i.val, by have := i.isLt; omega⟩

private theorem properArcGap_internal (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : paperAxisProperArcIndex g hg a) (hi : i.val ≠ 0) :
    0 < (properArcGapIndex g hg a i).val ∧
      (properArcGapIndex g hg a i).val + 2 < (paperAxisPeriodCutPoints g hg a).card := by
  have := i.isLt
  change 0 < i.val ∧ i.val + 2 < (paperAxisPeriodCutPoints g hg a).card
  omega

/-- Actual Q-valued continuous proper arcs: zero is the joined wrap arc,
and a positive index is its literal internal gap with the same index. -/
def paperAxisProperArc (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (i : paperAxisProperArcIndex g hg a) :
    C(unitInterval, paperIdealQuadrilateral) :=
  if i.val = 0 then (paperAxisPeriodWrapSubarc g hg a ha).toContinuousMap
  else (paperAxisPeriodGapSubarc g hg a (properArcGapIndex g hg a i)).toContinuousMap

/-- The exact original-axis parameter on every actual proper family member. -/
def paperAxisProperArcParameter (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : paperAxisProperArcIndex g hg a) (s : unitInterval) : ℝ :=
  if i.val = 0 then paperAxisWrapLeftTime g hg a +
    (paperAxisWrapRightTime g hg a - paperAxisWrapLeftTime g hg a) * (s : ℝ)
  else paperAxisPeriodGapParameter g hg a (properArcGapIndex g hg a i) s

/-- The actual cell label used to pull each proper member into original Q. -/
def paperAxisProperArcCellLabel (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : paperAxisProperArcIndex g hg a) : modularTraceSubgroup :=
  if i.val = 0 then paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a)
  else paperAxisPeriodGapCellLabel g hg a (properArcGapIndex g hg a i)

/-- There is exactly one proper arc per letter of the constructed period word. -/
theorem paperAxisProperArc_card (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    Fintype.card (paperAxisProperArcIndex g hg a) =
      (paperAxisPeriodCellWord g hg a).length := by
  rw [paperAxisPeriodCellWord_length]
  exact Fintype.card_fin _

/-- Every member of the constructed finite family is an actual closed embedding. -/
theorem paperAxisProperArc_isClosedEmbedding (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (i : paperAxisProperArcIndex g hg a) :
    IsClosedEmbedding (paperAxisProperArc g hg a ha i) := by
  by_cases hi : i.val = 0
  · simpa only [paperAxisProperArc, if_pos hi] using
      paperAxisPeriodWrapSubarc_isClosedEmbedding g hg a ha
  · simpa only [paperAxisProperArc, if_neg hi] using
      paperAxisPeriodGapSubarc_isClosedEmbedding g hg a (properArcGapIndex g hg a i)

/-- Every open family-member interior satisfies the actual strict Q inequalities. -/
theorem paperAxisProperArc_strict (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (i : paperAxisProperArcIndex g hg a)
    (s : unitInterval) (hs0 : 0 < (s : ℝ)) (hs1 : (s : ℝ) < 1) :
    (paperAxisProperArc g hg a ha i s : UpperHalfPlane) ∈
      paperIdealQuadrilateralStrictRegion := by
  by_cases hi : i.val = 0
  · simpa only [paperAxisProperArc, if_pos hi] using
      paperAxisPeriodWrapSubarc_strict g hg a ha s hs0 hs1
  · simpa only [paperAxisProperArc, if_neg hi] using
      paperAxisPeriodGapSubarc_strict g hg a (properArcGapIndex g hg a i) s hs0 hs1

/-- All proper family members have genuine uniquely labelled endpoints on
TWO DIFFERENT original sides, including the actual joined wrap member. -/
theorem paperAxisProperArc_endpoint_sides (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (i : paperAxisProperArcIndex g hg a) :
    ∃ k l : Fin 4, k ≠ l ∧
      (paperAxisProperArc g hg a ha i 0 : UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide k ∧
      (paperAxisProperArc g hg a ha i 1 : UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide l ∧
      (∀ k', (paperAxisProperArc g hg a ha i 0 : UpperHalfPlane) ∈
        paperQuadrilateralGeodesicSide k' → k' = k) ∧
      (∀ l', (paperAxisProperArc g hg a ha i 1 : UpperHalfPlane) ∈
        paperQuadrilateralGeodesicSide l' → l' = l) := by
  by_cases hi : i.val = 0
  · simpa only [paperAxisProperArc, if_pos hi] using
      paperAxisPeriodWrapSubarc_endpoint_sides g hg a ha
  · obtain ⟨hfirst, hlast⟩ := properArcGap_internal g hg a i hi
    simpa only [paperAxisProperArc, if_neg hi] using
      paperAxisPeriodGapSubarc_internal_endpoint_sides g hg a (properArcGapIndex g hg a i)
        hfirst hlast

/-- Applying the actual cell label recovers the displayed original-axis point. -/
theorem paperAxisProperArc_smul (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (i : paperAxisProperArcIndex g hg a) (s : unitInterval) :
    paperAxisProperArcCellLabel g hg a i • (paperAxisProperArc g hg a ha i s : UpperHalfPlane) =
      modularHyperbolicAxis g hg (paperAxisProperArcParameter g hg a i s) := by
  by_cases hi : i.val = 0
  · simpa only [paperAxisProperArc, paperAxisProperArcParameter,
      paperAxisProperArcCellLabel, if_pos hi] using
      paperAxisPeriodWrapSubarc_smul g hg a ha s
  · simpa only [paperAxisProperArc, paperAxisProperArcParameter,
      paperAxisProperArcCellLabel, if_neg hi] using
      paperAxisPeriodGapSubarc_smul g hg a (properArcGapIndex g hg a i) s

/-- Projection of every proper family member is literally its displayed axis point. -/
theorem paperAxisProperArc_project (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (i : paperAxisProperArcIndex g hg a) (s : unitInterval) :
    modularTraceQuotientMk (paperAxisProperArc g hg a ha i s) =
      modularTraceQuotientMk (modularHyperbolicAxis g hg
        (paperAxisProperArcParameter g hg a i s)) := by
  rw [← paperAxisProperArc_smul g hg a ha i s, modularTraceQuotientMk_smul]

end Markov
