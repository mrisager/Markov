import Markov.PaperAxisProperArcGluing
import Markov.PaperAxisWrapClosedDisjoint

/-! Actual finite endpoint tags, actual Q-values, and actual unique original
side labels of the complete proper-arc family. Endpoint-value injectivity is
proved from the actual closed-arc separation and actual arc embeddings. -/
noncomputable section
open Set Topology
namespace Markov

/-- A tag records the actual family member and its source/target endpoint. -/
abbrev paperAxisProperEndpointTag (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :=
  paperAxisProperArcIndex g hg a × Fin 2

/-- Endpoint zero is the actual source and endpoint one the actual target. -/
def paperAxisProperEndpointParameter (e : Fin 2) : unitInterval := ![0, 1] e

private theorem endpointParameter_injective : Function.Injective paperAxisProperEndpointParameter := by
  intro e f he
  fin_cases e <;> fin_cases f <;> norm_num [paperAxisProperEndpointParameter] at *

/-- The literal original-Q point of each actual tagged endpoint. -/
def paperAxisProperEndpointPoint (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a) :
    paperIdealQuadrilateral :=
  paperAxisProperArc g hg a ha t.1 (paperAxisProperEndpointParameter t.2)

private def endpointGapIndex (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : paperAxisProperArcIndex g hg a) : Fin ((paperAxisPeriodCutPoints g hg a).card - 1) :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- Distinct actual proper-family members have distinct values for ALL unit
parameters, including their closed endpoints and the joined wrap member. -/
theorem paperAxisProperArc_points_ne
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (i j : paperAxisProperArcIndex g hg a) (hij : i ≠ j) (s t : unitInterval) :
    paperAxisProperArc g hg a ha i s ≠ paperAxisProperArc g hg a ha j t := by
  have internal (k : paperAxisProperArcIndex g hg a) (hk : k.val ≠ 0) :
      0 < (endpointGapIndex g hg a k).val ∧
      (endpointGapIndex g hg a k).val + 2 < (paperAxisPeriodCutPoints g hg a).card := by
    have := k.isLt
    change 0 < k.val ∧ k.val + 2 < (paperAxisPeriodCutPoints g hg a).card
    omega
  by_cases hi : i.val = 0
  · have hj : j.val ≠ 0 := fun hj => hij (Fin.ext (hi.trans hj.symm))
    simpa only [paperAxisProperArc, if_pos hi, if_neg hj] using
      paperAxisPeriodWrapSubarc_ne_internalGap_closed g hg a ha hproject
        (endpointGapIndex g hg a j) (internal j hj).1 (internal j hj).2 s t
  · by_cases hj : j.val = 0
    · simpa only [paperAxisProperArc, if_neg hi, if_pos hj] using
        (paperAxisPeriodWrapSubarc_ne_internalGap_closed g hg a ha hproject
          (endpointGapIndex g hg a i) (internal i hi).1 (internal i hi).2 t s).symm
    · have hne : endpointGapIndex g hg a i ≠ endpointGapIndex g hg a j := by
        intro he
        have hv : i.val = j.val := congrArg
          (fun k : Fin ((paperAxisPeriodCutPoints g hg a).card - 1) => k.val) he
        exact hij (Fin.ext hv)
      simpa only [paperAxisProperArc, if_neg hi, if_neg hj] using
        paperAxisPeriodGapSubarc_internal_points_ne g hg a (hproject a)
          (endpointGapIndex g hg a i) (endpointGapIndex g hg a j) hne
          (internal i hi).1 (internal i hi).2 (internal j hj).1 (internal j hj).2 s t

/-- Distinct actual endpoint tags determine distinct actual Q-points, proved
from genuine closed-arc separation and genuine arc injectivity. -/
theorem paperAxisProperEndpointPoint_injective
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) :
    Function.Injective (paperAxisProperEndpointPoint g hg a ha) := by
  rintro ⟨i, e⟩ ⟨j, f⟩ he
  have hij : i = j := by
    by_contra hne
    exact paperAxisProperArc_points_ne g hg a ha hproject i j hne _ _ he
  subst j
  have hp := (paperAxisProperArc_isClosedEmbedding g hg a ha i).injective he
  exact Prod.ext rfl (endpointParameter_injective hp)

private theorem endpoint_existsUnique_side
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a) :
    ∃! k : Fin 4, (paperAxisProperEndpointPoint g hg a ha t : UpperHalfPlane) ∈
      paperQuadrilateralGeodesicSide k := by
  obtain ⟨k, l, _, hk, hl, hku, hlu⟩ := paperAxisProperArc_endpoint_sides g hg a ha t.1
  rcases t with ⟨i,e⟩
  fin_cases e
  · exact ⟨k, hk, hku⟩
  · exact ⟨l, hl, hlu⟩

/-- The side label is constructed from actual unique original-side membership. -/
def paperAxisProperEndpointSide (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a) : Fin 4 :=
  (endpoint_existsUnique_side g hg a ha t).choose

/-- Every constructed endpoint lies on its actual constructed original side. -/
theorem paperAxisProperEndpointSide_spec (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a) :
    (paperAxisProperEndpointPoint g hg a ha t : UpperHalfPlane) ∈
      paperQuadrilateralGeodesicSide (paperAxisProperEndpointSide g hg a ha t) :=
  (endpoint_existsUnique_side g hg a ha t).choose_spec.1

/-- Literal side membership uniquely recovers the constructed endpoint label. -/
theorem paperAxisProperEndpointSide_unique (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a)
    (k : Fin 4) (hk : (paperAxisProperEndpointPoint g hg a ha t : UpperHalfPlane) ∈
      paperQuadrilateralGeodesicSide k) : k = paperAxisProperEndpointSide g hg a ha t :=
  (endpoint_existsUnique_side g hg a ha t).choose_spec.2 k hk

/-- The literal tagged endpoint set has exactly twice the actual word length. -/
theorem paperAxisProperEndpointTag_card (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    Fintype.card (paperAxisProperEndpointTag g hg a) =
      2 * (paperAxisPeriodCellWord g hg a).length := by
  rw [Fintype.card_prod, paperAxisProperArc_card]
  rw [Fintype.card_fin, mul_comm]

end Markov
