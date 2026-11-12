import Markov.PaperAxisWrapSubarc

/-! The genuine wrap arc is disjoint from every genuine internal gap arc
under actual projected-axis period injectivity. Real parameter bounds are
proved from the actual ordered table, not supplied as diagram fields. -/
noncomputable section
open Set Topology
namespace Markov

/-- The literal affine real parameter of the constructed joined wrap arc. -/
def paperAxisPeriodWrapParameter
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (s : unitInterval) : ℝ :=
  paperAxisWrapLeftTime g hg a +
    (paperAxisWrapRightTime g hg a-paperAxisWrapLeftTime g hg a)*(s:ℝ)

/-- Every open wrap parameter lies strictly between the actual wrap endpoints. -/
theorem paperAxisPeriodWrapParameter_mem_interval
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (s : unitInterval) (hs0 : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1) :
    paperAxisPeriodWrapParameter g hg a s ∈
      Ioo (paperAxisWrapLeftTime g hg a) (paperAxisWrapRightTime g hg a) := by
  have hlt := lt_trans (paperAxisWrapTimes_straddle g hg a).1
    (paperAxisWrapTimes_straddle g hg a).2
  dsimp only [paperAxisPeriodWrapParameter]
  constructor <;> nlinarith

/-- Actual wrap and internal-gap open parameters lie in ONE actual open period
based at the wrap left endpoint, with the wrap parameter strictly first. -/
theorem paperAxisWrap_internalGap_parameters_one_period
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card-1))
    (hfirst : 0 < i.val) (hlast : i.val+2 < (paperAxisPeriodCutPoints g hg a).card)
    (s t : unitInterval) (hs0 : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1)
    (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) :
    paperAxisPeriodWrapParameter g hg a s ∈
        Ioo (paperAxisWrapLeftTime g hg a)
          (paperAxisWrapLeftTime g hg a+modularClosedGeodesicPeriod g) ∧
      paperAxisPeriodGapParameter g hg a i t ∈
        Ioo (paperAxisWrapLeftTime g hg a)
          (paperAxisWrapLeftTime g hg a+modularClosedGeodesicPeriod g) ∧
      paperAxisPeriodWrapParameter g hg a s < paperAxisPeriodGapParameter g hg a i t := by
  have hleftIndex : paperAxisGapRightIndex g hg a (paperAxisFirstGapIndex g hg a) ≤
      paperAxisGapLeftIndex g hg a i := by
    change 0+1 ≤ i.val
    omega
  have hrightIndex : paperAxisGapRightIndex g hg a i ≤
      paperAxisGapLeftIndex g hg a (paperAxisLastGapIndex g hg a) := by
    change i.val+1 ≤ (paperAxisPeriodCutPoints g hg a).card-2
    omega
  have hleft := (paperAxisPeriodCutTable g hg a).monotone hleftIndex
  have hright := (paperAxisPeriodCutTable g hg a).monotone hrightIndex
  have hs := paperAxisPeriodWrapParameter_mem_interval g hg a s hs0 hs1
  have ht := paperAxisPeriodGapParameter_mem_gap g hg a i t ht0 ht1
  have horder : paperAxisPeriodWrapParameter g hg a s <
      paperAxisPeriodGapParameter g hg a i t := (hs.2.trans_le hleft).trans ht.1
  have hupper : paperAxisPeriodGapParameter g hg a i t <
      paperAxisWrapLeftTime g hg a+modularClosedGeodesicPeriod g := by
    have he : paperAxisPeriodCutTable g hg a
        (paperAxisGapLeftIndex g hg a (paperAxisLastGapIndex g hg a)) =
        paperAxisWrapLeftTime g hg a+modularClosedGeodesicPeriod g := by
      dsimp only [paperAxisWrapLeftTime]
      ring
    rw [← he]
    exact ht.2.trans_le hright
  exact ⟨⟨hs.1,horder.trans hupper⟩,⟨hs.1.trans horder,hupper⟩,horder⟩

/-- Literal quotient projections and actual period injectivity exclude equality
of any open wrap-arc point and any open internal-gap-arc point. -/
theorem paperAxisPeriodWrapSubarc_ne_internalGap_of_projected_period_injective
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card-1))
    (hfirst : 0 < i.val) (hlast : i.val+2 < (paperAxisPeriodCutPoints g hg a).card)
    (s t : unitInterval) (hs0 : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1)
    (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) :
    paperAxisPeriodWrapSubarc g hg a ha s ≠ paperAxisPeriodGapSubarc g hg a i t := by
  intro heq
  have hbounds := paperAxisWrap_internalGap_parameters_one_period g hg a i hfirst hlast
    s t hs0 hs1 ht0 ht1
  have hp := congrArg (fun z : paperIdealQuadrilateral => modularTraceQuotientMk z) heq
  change modularTraceQuotientMk (paperAxisPeriodWrapSubarc g hg a ha s) =
    modularTraceQuotientMk (paperAxisPeriodGapSubarc g hg a i t) at hp
  rw [paperAxisPeriodWrapSubarc_project, paperAxisPeriodGapSubarc_project] at hp
  change modularTraceQuotientMk (modularHyperbolicAxis g hg
      (paperAxisPeriodWrapParameter g hg a s)) =
    modularTraceQuotientMk (modularHyperbolicAxis g hg (paperAxisPeriodGapParameter g hg a i t)) at hp
  have htime := (hproject (paperAxisWrapLeftTime g hg a)) hbounds.1 hbounds.2.1 hp
  exact hbounds.2.2.ne htime

/-- The actual open image of the genuine wrap arc is disjoint from each
actual internal normal-gap open image. No matching/classification field is used. -/
theorem paperAxisPeriodWrapSubarc_internalGap_interiors_disjoint
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card-1))
    (hfirst : 0 < i.val) (hlast : i.val+2 < (paperAxisPeriodCutPoints g hg a).card) :
    Disjoint ((paperAxisPeriodWrapSubarc g hg a ha) '' Ioo (0:unitInterval) 1)
      ((paperAxisPeriodGapSubarc g hg a i) '' Ioo (0:unitInterval) 1) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨s,hs,hsx⟩ ⟨t,ht,htx⟩
  exact paperAxisPeriodWrapSubarc_ne_internalGap_of_projected_period_injective
    g hg a ha hproject i hfirst hlast s t hs.1 hs.2 ht.1 ht.2 (hsx.trans htx.symm)

end Markov
