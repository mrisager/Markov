import Markov.ModularSimpleMetricCircleEndpointData

/-! Actual proper Q-arcs oriented from any genuine tagged endpoint toward
its actual ARC partner. These provide concrete arcs for corner-crossing
applications; no endpoint ordering or pairing field is supplied. -/
noncomputable section
open Set Topology
namespace Markov

/-- The actual family arc, parameter-reversed exactly when its tagged source
is its original target; its displayed endpoints are the actual tagged points. -/
def paperAxisArcFromTag (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a) :
    Path (paperAxisProperEndpointPoint g hg a ha t)
      (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t)) where
  toFun s := if t.2 = 0 then paperAxisProperArc g hg a ha t.1 s
    else paperAxisProperArc g hg a ha t.1 (unitInterval.symm s)
  continuous_toFun := by
    by_cases he : t.2 = 0
    · simpa only [if_pos he] using (paperAxisProperArc g hg a ha t.1).continuous
    · simpa only [if_neg he] using
        (paperAxisProperArc g hg a ha t.1).continuous.comp unitInterval.continuous_symm
  source' := by
    rcases t with ⟨i,e⟩
    fin_cases e
    · rfl
    · change paperAxisProperArc g hg a ha i (unitInterval.symm 0) = paperAxisProperArc g hg a ha i 1
      rw [unitInterval.symm_zero]
  target' := by
    rcases t with ⟨i,e⟩
    fin_cases e
    · rfl
    · change paperAxisProperArc g hg a ha i (unitInterval.symm 1) = paperAxisProperArc g hg a ha i 0
      rw [unitInterval.symm_one]

/-- Every actually oriented tagged arc remains a closed embedding. -/
theorem paperAxisArcFromTag_isClosedEmbedding (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a) :
    IsClosedEmbedding (paperAxisArcFromTag g hg a ha t) := by
  apply (paperAxisArcFromTag g hg a ha t).continuous.isClosedEmbedding
  by_cases he : t.2 = 0
  · simpa only [paperAxisArcFromTag,if_pos he] using
      (paperAxisProperArc_isClosedEmbedding g hg a ha t.1).injective
  · simpa only [paperAxisArcFromTag,if_neg he] using
      (paperAxisProperArc_isClosedEmbedding g hg a ha t.1).injective.comp unitInterval.symmHomeomorph.injective

/-- Reversing the actual unit parameter preserves the true strict Q interior. -/
theorem paperAxisArcFromTag_strict (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a)
    (s : unitInterval) (hs0 : 0 < (s : ℝ)) (hs1 : (s : ℝ) < 1) :
    (paperAxisArcFromTag g hg a ha t s : UpperHalfPlane) ∈ paperIdealQuadrilateralStrictRegion := by
  by_cases he : t.2 = 0
  · simpa only [paperAxisArcFromTag,if_pos he] using
      paperAxisProperArc_strict g hg a ha t.1 s hs0 hs1
  · have hr0 : 0 < ((unitInterval.symm s : unitInterval) : ℝ) := by
      change 0 < 1-(s : ℝ)
      linarith
    have hr1 : ((unitInterval.symm s : unitInterval) : ℝ) < 1 := by
      change 1-(s : ℝ) < 1
      linarith
    simpa only [paperAxisArcFromTag,if_neg he] using
      paperAxisProperArc_strict g hg a ha t.1 (unitInterval.symm s) hr0 hr1

/-- Different tagged endpoints on the same actual literal side belong to
DIFFERENT actual proper arcs, by genuine different-side arc endpoints. -/
theorem paperAxisProperEndpoint_same_side_arcIndex_ne (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t u : paperAxisProperEndpointTag g hg a)
    (hne : t ≠ u) (hside : paperAxisProperEndpointSide g hg a ha t =
      paperAxisProperEndpointSide g hg a ha u) : t.1 ≠ u.1 := by
  rcases t with ⟨i,e⟩
  rcases u with ⟨j,f⟩
  intro hij
  change i = j at hij
  subst j
  fin_cases e <;> fin_cases f
  · exact hne rfl
  · exact paperAxisProperArcEndpointPair_sides_ne g hg a ha (i,0) hside.symm
  · exact paperAxisProperArcEndpointPair_sides_ne g hg a ha (i,1) hside.symm
  · exact hne rfl

/-- Distinct actual arc indices give disjoint tagged-arc values for ALL unit
parameters, including the genuine tagged endpoints. -/
theorem paperAxisArcFromTag_points_ne (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (t u : paperAxisProperEndpointTag g hg a) (hne : t.1 ≠ u.1) (s v : unitInterval) :
    paperAxisArcFromTag g hg a ha t s ≠ paperAxisArcFromTag g hg a ha u v := by
  by_cases he : t.2 = 0 <;> by_cases hf : u.2 = 0
  · simpa only [paperAxisArcFromTag,if_pos he,if_pos hf] using
      paperAxisProperArc_points_ne g hg a ha hproject t.1 u.1 hne s v
  · simpa only [paperAxisArcFromTag,if_pos he,if_neg hf] using
      paperAxisProperArc_points_ne g hg a ha hproject t.1 u.1 hne s (unitInterval.symm v)
  · simpa only [paperAxisArcFromTag,if_neg he,if_pos hf] using
      paperAxisProperArc_points_ne g hg a ha hproject t.1 u.1 hne (unitInterval.symm s) v
  · simpa only [paperAxisArcFromTag,if_neg he,if_neg hf] using
      paperAxisProperArc_points_ne g hg a ha hproject t.1 u.1 hne (unitInterval.symm s) (unitInterval.symm v)

end Markov
