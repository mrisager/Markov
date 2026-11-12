import Markov.PaperAxisProperEndpointTags

/-! Actual arc and quotient-edge endpoint pairings of the constructed proper
family. Both permutations are constructed from the literal tagged endpoints,
with actual arc membership and actual projected gluing, never matching fields. -/
noncomputable section
open Set Topology
namespace Markov

private def endpointArcFlip (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (t : paperAxisProperEndpointTag g hg a) : paperAxisProperEndpointTag g hg a :=
  (t.1, t.2.rev)

private theorem endpointArcFlip_involutive (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    Function.Involutive (endpointArcFlip g hg a) := by
  rintro ⟨i,e⟩
  simp [endpointArcFlip]

/-- Pair the actual source and target of each actual proper arc. -/
def paperAxisProperArcEndpointPair (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    Equiv.Perm (paperAxisProperEndpointTag g hg a) where
  toFun := endpointArcFlip g hg a
  invFun := endpointArcFlip g hg a
  left_inv := endpointArcFlip_involutive g hg a
  right_inv := endpointArcFlip_involutive g hg a

/-- The actual arc pairing is an involution. -/
theorem paperAxisProperArcEndpointPair_involutive (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    Function.Involutive (paperAxisProperArcEndpointPair g hg a) :=
  endpointArcFlip_involutive g hg a

/-- The two actual endpoints of an arc have different tags. -/
theorem paperAxisProperArcEndpointPair_ne (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (t : paperAxisProperEndpointTag g hg a) : paperAxisProperArcEndpointPair g hg a t ≠ t := by
  rcases t with ⟨i,e⟩
  intro he
  have hv := congrArg (fun t : paperAxisProperEndpointTag g hg a => t.2) he
  fin_cases e <;> norm_num [paperAxisProperArcEndpointPair, endpointArcFlip, Fin.rev] at hv

/-- The actual previous arc in the finite cyclic proper-family order. -/
def paperAxisProperArcPrevIndex (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : paperAxisProperArcIndex g hg a) : paperAxisProperArcIndex g hg a :=
  if i.val = 0 then
    ⟨(paperAxisPeriodCutPoints g hg a).card - 2 - 1, by have := i.isLt; omega⟩
  else ⟨i.val - 1, by have := i.isLt; omega⟩

/-- The literal cyclic predecessor reverses the actual successor. -/
theorem paperAxisProperArcPrevIndex_next (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : paperAxisProperArcIndex g hg a) :
    paperAxisProperArcPrevIndex g hg a (paperAxisProperArcNextIndex g hg a i) = i := by
  apply Fin.ext
  have := i.isLt
  unfold paperAxisProperArcPrevIndex paperAxisProperArcNextIndex
  split_ifs <;> dsimp only at * <;> omega

/-- The actual successor reverses the literal cyclic predecessor. -/
theorem paperAxisProperArcNextIndex_prev (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : paperAxisProperArcIndex g hg a) :
    paperAxisProperArcNextIndex g hg a (paperAxisProperArcPrevIndex g hg a i) = i := by
  have hinj : Function.Injective (paperAxisProperArcNextIndex g hg a) := by
    intro j k he
    have hp := congrArg (paperAxisProperArcPrevIndex g hg a) he
    simpa only [paperAxisProperArcPrevIndex_next] using hp
  obtain ⟨j, rfl⟩ := Finite.surjective_of_injective hinj i
  rw [paperAxisProperArcPrevIndex_next]

private def endpointEdgeFlip (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (t : paperAxisProperEndpointTag g hg a) : paperAxisProperEndpointTag g hg a :=
  if t.2 = 0 then (paperAxisProperArcPrevIndex g hg a t.1, 1)
  else (paperAxisProperArcNextIndex g hg a t.1, 0)

private theorem endpointEdgeFlip_involutive (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    Function.Involutive (endpointEdgeFlip g hg a) := by
  rintro ⟨i,e⟩
  fin_cases e <;> simp [endpointEdgeFlip, paperAxisProperArcNextIndex_prev,
    paperAxisProperArcPrevIndex_next]

/-- Pair each target with the next actual source, and each source with the
previous actual target, using the genuinely constructed cyclic gluing. -/
def paperAxisProperEdgePair (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    Equiv.Perm (paperAxisProperEndpointTag g hg a) where
  toFun := endpointEdgeFlip g hg a
  invFun := endpointEdgeFlip g hg a
  left_inv := endpointEdgeFlip_involutive g hg a
  right_inv := endpointEdgeFlip_involutive g hg a

/-- The actual quotient-edge pairing is an involution. -/
theorem paperAxisProperEdgePair_involutive (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    Function.Involutive (paperAxisProperEdgePair g hg a) :=
  endpointEdgeFlip_involutive g hg a

/-- Actual edge-paired tags are different, including one-arc families. -/
theorem paperAxisProperEdgePair_ne (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (t : paperAxisProperEndpointTag g hg a) : paperAxisProperEdgePair g hg a t ≠ t := by
  rcases t with ⟨i,e⟩
  intro he
  have hv := congrArg (fun t : paperAxisProperEndpointTag g hg a => t.2) he
  fin_cases e <;> norm_num [paperAxisProperEdgePair, endpointEdgeFlip] at hv

/-- The constructed edge pairing identifies the actual quotient points. -/
theorem paperAxisProperEdgePair_project (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a) :
    modularTraceQuotientMk (paperAxisProperEndpointPoint g hg a ha t) =
      modularTraceQuotientMk (paperAxisProperEndpointPoint g hg a ha
        (paperAxisProperEdgePair g hg a t)) := by
  rcases t with ⟨i,e⟩
  fin_cases e
  · change modularTraceQuotientMk (paperAxisProperArc g hg a ha i 0) =
      modularTraceQuotientMk (paperAxisProperArc g hg a ha (paperAxisProperArcPrevIndex g hg a i) 1)
    have he := paperAxisProperArc_projected_gluing g hg a ha (paperAxisProperArcPrevIndex g hg a i)
    rw [paperAxisProperArcNextIndex_prev] at he
    exact he.symm
  · exact paperAxisProperArc_projected_gluing g hg a ha i

/-- Actual edge-paired endpoint values are distinct Q-points; this is derived
from the actual geometric tagged-point injection, never assumed. -/
theorem paperAxisProperEdgePair_points_ne (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (t : paperAxisProperEndpointTag g hg a) :
    paperAxisProperEndpointPoint g hg a ha t ≠ paperAxisProperEndpointPoint g hg a ha
      (paperAxisProperEdgePair g hg a t) := by
  intro he
  exact paperAxisProperEdgePair_ne g hg a t
    ((paperAxisProperEndpointPoint_injective g hg a ha hproject he).symm)

end Markov
