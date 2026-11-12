import Markov.PaperAxisCornerFrameBarrier
import Markov.PaperAxisBoundaryRanks

/-! Genuine nearest-corner ARC pairing in ALL four actual Q corners. The
actual oriented lists and actual complex frame crossing discharge all rank,
order and nearest-pair assertions. No extrema SET or classifier is assumed. -/
noncomputable section
open Set Topology
namespace Markov

private theorem allCorner_mem
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (t : paperAxisProperEndpointTag g hg a) (k : Fin 4)
    (ht : paperAxisProperEndpointSide g hg a ha t = k) :
    (paperAxisProperEndpointPoint g hg a ha t : UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide k := by
  simpa only [ht] using paperAxisProperEndpointSide_spec g hg a ha t

private theorem allCorner_boundary_eq_tag
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (s t : paperAxisProperEndpointTag g hg a) (k : Fin 4)
    (hs : paperAxisProperEndpointSide g hg a ha s = k)
    (ht : paperAxisProperEndpointSide g hg a ha t = k)
    (he : paperAxisProperEndpointBoundaryCoordinate g hg a ha s =
      paperAxisProperEndpointBoundaryCoordinate g hg a ha t) : s=t := by
  classical
  have hsign (v : paperAxisProperEndpointTag g hg a) (hv : paperAxisProperEndpointSide g hg a ha v = k) :
      paperAxisProperEndpointBoundaryCoordinate g hg a ha v =
        if k=1 ∨ k=2 then -paperAxisProperEndpointCoordinate g hg a ha v
        else paperAxisProperEndpointCoordinate g hg a ha v := by
    unfold paperAxisProperEndpointBoundaryCoordinate paperAxisProperEndpointCoordinate
    rw [hv]
    fin_cases k <;> rfl
  have hc : paperAxisProperEndpointCoordinate g hg a ha s = paperAxisProperEndpointCoordinate g hg a ha t := by
    rw [hsign s hs,hsign t ht] at he
    by_cases hk : k=1 ∨ k=2
    · simp only [if_pos hk] at he
      exact neg_injective he
    · simpa only [if_neg hk] using he
  exact paperAxisProperEndpointCoordinate_injOn_side g hg a ha hproject k
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩) hc

private theorem allCorner_source_lt
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) (s t : paperAxisProperEndpointTag g hg a)
    (hs : paperAxisProperEndpointSide g hg a ha s = k) (ht : paperAxisProperEndpointSide g hg a ha t = k)
    (he : paperAxisProperEndpointBoundaryCoordinate g hg a ha s < paperAxisProperEndpointBoundaryCoordinate g hg a ha t) :
    (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha s)).re <
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha t)).re := by
  have hm : paperQuadrilateralBoundarySideCoordinate k (paperAxisProperEndpointPoint g hg a ha s) <
      paperQuadrilateralBoundarySideCoordinate k (paperAxisProperEndpointPoint g hg a ha t) := by
    simpa only [paperAxisProperEndpointBoundaryCoordinate,hs,ht] using he
  have hr := (paperQuadrilateralBoundarySideCoordinate_raw_lt_iff k _ _
    (allCorner_mem g hg a ha s k hs) (allCorner_mem g hg a ha t k ht)).mp hm
  simpa only [paperQuadrilateralRawSideFrame_re] using hr

private theorem allCorner_source_le
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) (s t : paperAxisProperEndpointTag g hg a)
    (hs : paperAxisProperEndpointSide g hg a ha s = k) (ht : paperAxisProperEndpointSide g hg a ha t = k)
    (he : (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha s)).re ≤
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha t)).re) :
    paperAxisProperEndpointBoundaryCoordinate g hg a ha s ≤ paperAxisProperEndpointBoundaryCoordinate g hg a ha t := by
  have hr : paperQuadrilateralRawBoundarySideCoordinate k (paperAxisProperEndpointPoint g hg a ha s) ≤
      paperQuadrilateralRawBoundarySideCoordinate k (paperAxisProperEndpointPoint g hg a ha t) := by
    simpa only [paperQuadrilateralRawSideFrame_re] using he
  have hm := (paperQuadrilateralBoundarySideCoordinate_raw_le_iff k _ _
    (allCorner_mem g hg a ha s k hs) (allCorner_mem g hg a ha t k ht)).mpr hr
  simpa only [paperAxisProperEndpointBoundaryCoordinate,hs,ht] using hm

private theorem allCorner_next_lt
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) (s t : paperAxisProperEndpointTag g hg a)
    (hs : paperAxisProperEndpointSide g hg a ha s = paperQuadrilateralNextSide k)
    (ht : paperAxisProperEndpointSide g hg a ha t = paperQuadrilateralNextSide k)
    (he : paperAxisProperEndpointBoundaryCoordinate g hg a ha s < paperAxisProperEndpointBoundaryCoordinate g hg a ha t) :
    (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha t)).im <
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha s)).im := by
  have hm : paperQuadrilateralBoundarySideCoordinate (paperQuadrilateralNextSide k) (paperAxisProperEndpointPoint g hg a ha s) <
      paperQuadrilateralBoundarySideCoordinate (paperQuadrilateralNextSide k) (paperAxisProperEndpointPoint g hg a ha t) := by
    simpa only [paperAxisProperEndpointBoundaryCoordinate,hs,ht] using he
  have hr := (paperQuadrilateralBoundarySideCoordinate_raw_lt_iff (paperQuadrilateralNextSide k) _ _
    (allCorner_mem g hg a ha s _ hs) (allCorner_mem g hg a ha t _ ht)).mp hm
  simpa only [paperQuadrilateralRawSideFrame_im] using neg_lt_neg hr

private theorem allCorner_next_le
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) (s t : paperAxisProperEndpointTag g hg a)
    (hs : paperAxisProperEndpointSide g hg a ha s = paperQuadrilateralNextSide k)
    (ht : paperAxisProperEndpointSide g hg a ha t = paperQuadrilateralNextSide k)
    (he : (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha s)).im ≤
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha t)).im) :
    paperAxisProperEndpointBoundaryCoordinate g hg a ha t ≤ paperAxisProperEndpointBoundaryCoordinate g hg a ha s := by
  have hn : -paperQuadrilateralRawBoundarySideCoordinate (paperQuadrilateralNextSide k) (paperAxisProperEndpointPoint g hg a ha s) ≤
      -paperQuadrilateralRawBoundarySideCoordinate (paperQuadrilateralNextSide k) (paperAxisProperEndpointPoint g hg a ha t) := by
    simpa only [paperQuadrilateralRawSideFrame_im] using he
  have hm := (paperQuadrilateralBoundarySideCoordinate_raw_le_iff (paperQuadrilateralNextSide k) _ _
    (allCorner_mem g hg a ha t _ ht) (allCorner_mem g hg a ha s _ hs)).mpr (neg_le_neg_iff.mp hn)
  simpa only [paperAxisProperEndpointBoundaryCoordinate,hs,ht] using hm

private theorem allCorner_source_bounds (k : Fin 4) (z : paperIdealQuadrilateral)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide k) :
    -1<(paperQuadrilateralRawSideFrame k z).re ∧ (paperQuadrilateralRawSideFrame k z).re<1 := by
  rw [paperQuadrilateralRawSideFrame_re]
  exact paperQuadrilateralRawBoundarySideCoordinate_bounds k z hz

private theorem allCorner_next_bounds (k : Fin 4) (z : paperIdealQuadrilateral)
    (hz : z.val ∈ paperQuadrilateralGeodesicSide (paperQuadrilateralNextSide k)) :
    -1<(paperQuadrilateralRawSideFrame k z).im ∧ (paperQuadrilateralRawSideFrame k z).im<1 := by
  rw [paperQuadrilateralRawSideFrame_im]
  have hb := paperQuadrilateralRawBoundarySideCoordinate_bounds _ z hz
  constructor <;> linarith [hb.1,hb.2]

/-- At every actual corner, a source-side endpoint nearer the corner must
pair to a next-side endpoint nearer the same corner. This packet-order fact
is derived from actual crossing, not supplied as an order field. -/
theorem paperAxisCorner_source_nearer_partner
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (k : Fin 4) (s t : paperAxisProperEndpointTag g hg a)
    (hs : paperAxisProperEndpointSide g hg a ha s = k)
    (hp : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a s) = paperQuadrilateralNextSide k)
    (ht : paperAxisProperEndpointSide g hg a ha t = k)
    (hlt : paperAxisProperEndpointBoundaryCoordinate g hg a ha s < paperAxisProperEndpointBoundaryCoordinate g hg a ha t) :
    paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) = paperQuadrilateralNextSide k ∧
      paperAxisProperEndpointBoundaryCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a t) <
        paperAxisProperEndpointBoundaryCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a s) := by
  have hne : s≠t := by intro he; subst t; exact (lt_irrefl _) hlt
  have hi := paperAxisProperEndpoint_same_side_arcIndex_ne g hg a ha s t hne (hs.trans ht.symm)
  have hraw := allCorner_source_lt g hg a ha k s t hs ht hlt
  have hb := allCorner_next_bounds k _ (allCorner_mem g hg a ha _ _ hp)
  have hpos : 0<rawSquareCorner01Cap
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha s)).re
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha t)) := by
    simpa only [rawSquareCorner01Cap,(paperQuadrilateralRawSideFrame_top k _ (allCorner_mem g hg a ha t k ht)).1,
      sub_self,mul_zero,add_zero] using mul_pos (sub_pos.mpr hb.2) (sub_pos.mpr hraw)
  have hc := paperAxisCorner_cap_partner_nonnegative g hg a ha hproject k s t hs hp hi hpos
  have ha' := allCorner_source_bounds k _ (allCorner_mem g hg a ha s k hs)
  have hcases := paperQuadrilateralFrame_nonnegative_cap_sides k _ _ ha' hb
    (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t)) _
    (paperAxisProperEndpointSide_spec g hg a ha (paperAxisProperArcEndpointPair g hg a t)) hc
  have hpt : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) = paperQuadrilateralNextSide k := by
    rcases hcases with h0 | h1
    · exact False.elim ((paperAxisProperArcEndpointPair_sides_ne g hg a ha t) (h0.trans ht.symm))
    · exact h1
  have heq : rawSquareCorner01Cap
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha s)).re
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t))) =
      (1-(paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha s)).re)*
        ((paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t))).im-
          (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im) := by
    rw [rawSquareCorner01Cap,(paperQuadrilateralRawSideFrame_right k _ (allCorner_mem g hg a ha _ _ hpt)).1]
    ring
  rw [heq] at hc
  have hle : (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im ≤
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t))).im := by
    by_contra hn
    exact not_lt_of_ge hc (mul_neg_of_pos_of_neg (sub_pos.mpr ha'.2) (sub_neg.mpr (lt_of_not_ge hn)))
  have hm := allCorner_next_le g hg a ha k _ _ hp hpt hle
  refine ⟨hpt,lt_of_le_of_ne hm ?_⟩
  intro he
  have htags := allCorner_boundary_eq_tag g hg a ha hproject _ _ _ hpt hp he
  exact hne ((paperAxisProperArcEndpointPair g hg a).injective htags).symm

/-- At every actual corner, a next-side endpoint nearer the corner must
pair to a source-side endpoint nearer the same corner. -/
theorem paperAxisCorner_next_nearer_partner
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (k : Fin 4) (s t : paperAxisProperEndpointTag g hg a)
    (hs : paperAxisProperEndpointSide g hg a ha s = k)
    (hp : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a s) = paperQuadrilateralNextSide k)
    (ht : paperAxisProperEndpointSide g hg a ha t = paperQuadrilateralNextSide k)
    (hlt : paperAxisProperEndpointBoundaryCoordinate g hg a ha t <
      paperAxisProperEndpointBoundaryCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a s)) :
    paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) = k ∧
      paperAxisProperEndpointBoundaryCoordinate g hg a ha s <
        paperAxisProperEndpointBoundaryCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a t) := by
  have hne : paperAxisProperArcEndpointPair g hg a s ≠ t := by intro he; rw [he] at hlt; exact (lt_irrefl _) hlt
  have hi : s.1 ≠ t.1 := paperAxisProperEndpoint_same_side_arcIndex_ne g hg a ha
    (paperAxisProperArcEndpointPair g hg a s) t hne (hp.trans ht.symm)
  have hraw := allCorner_next_lt g hg a ha k t _ ht hp hlt
  have ha' := allCorner_source_bounds k _ (allCorner_mem g hg a ha s k hs)
  have heq0 : rawSquareCorner01Cap
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha s)).re
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha t)) =
      (1-(paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha s)).re)*
        ((paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha t)).im-
          (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im) := by
    rw [rawSquareCorner01Cap,(paperQuadrilateralRawSideFrame_right k _ (allCorner_mem g hg a ha t _ ht)).1]
    ring
  have hpos : 0<rawSquareCorner01Cap
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha s)).re
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha t)) := by
    rw [heq0]
    exact mul_pos (sub_pos.mpr ha'.2) (sub_pos.mpr hraw)
  have hc := paperAxisCorner_cap_partner_nonnegative g hg a ha hproject k s t hs hp hi hpos
  have hb := allCorner_next_bounds k _ (allCorner_mem g hg a ha _ _ hp)
  have hcases := paperQuadrilateralFrame_nonnegative_cap_sides k _ _ ha' hb
    (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t)) _
    (paperAxisProperEndpointSide_spec g hg a ha (paperAxisProperArcEndpointPair g hg a t)) hc
  have hpt : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t) = k := by
    rcases hcases with h0 | h1
    · exact h0
    · exact False.elim ((paperAxisProperArcEndpointPair_sides_ne g hg a ha t) (h1.trans ht.symm))
  have heq : rawSquareCorner01Cap
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha s)).re
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t))) =
      (1-(paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a s))).im)*
        ((paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t))).re-
          (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha s)).re) := by
    simp only [rawSquareCorner01Cap,(paperQuadrilateralRawSideFrame_top k _ (allCorner_mem g hg a ha _ k hpt)).1,
      sub_self,mul_zero,add_zero]
  rw [heq] at hc
  have hle : (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha s)).re ≤
      (paperQuadrilateralRawSideFrame k (paperAxisProperEndpointPoint g hg a ha (paperAxisProperArcEndpointPair g hg a t))).re := by
    by_contra hn
    exact not_lt_of_ge hc (mul_neg_of_pos_of_neg (sub_pos.mpr hb.2) (sub_neg.mpr (lt_of_not_ge hn)))
  have hm := allCorner_source_le g hg a ha k _ _ hs hpt hle
  refine ⟨hpt,lt_of_le_of_ne hm ?_⟩
  intro he
  have htags := allCorner_boundary_eq_tag g hg a ha hproject s _ k hs hpt he
  have htEq : t = paperAxisProperArcEndpointPair g hg a s := by
    calc
      t = paperAxisProperArcEndpointPair g hg a (paperAxisProperArcEndpointPair g hg a t) :=
        (paperAxisProperArcEndpointPair_involutive g hg a t).symm
      _ = paperAxisProperArcEndpointPair g hg a s := congrArg (paperAxisProperArcEndpointPair g hg a) htags.symm
  exact hne htEq.symm

/-- At EVERY actual corner having any corner arc, the source-side boundary
maximum and next-side boundary minimum are genuinely ARC-paired. -/
theorem paperAxisCorner_extrema_arc_paired
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (k : Fin 4) (t u : paperAxisProperEndpointTag g hg a)
    (ht : paperAxisProperEndpointSide g hg a ha t = k)
    (hu : paperAxisProperEndpointSide g hg a ha u = paperQuadrilateralNextSide k)
    (hmax : ∀ v, paperAxisProperEndpointSide g hg a ha v=k →
      paperAxisProperEndpointBoundaryCoordinate g hg a ha v ≤ paperAxisProperEndpointBoundaryCoordinate g hg a ha t)
    (hmin : ∀ v, paperAxisProperEndpointSide g hg a ha v=paperQuadrilateralNextSide k →
      paperAxisProperEndpointBoundaryCoordinate g hg a ha u ≤ paperAxisProperEndpointBoundaryCoordinate g hg a ha v)
    (hcorner : ∃ s : paperAxisProperEndpointTag g hg a,
      paperAxisProperEndpointSide g hg a ha s=k ∧
        paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a s)=paperQuadrilateralNextSide k) :
    paperAxisProperArcEndpointPair g hg a t = u := by
  obtain ⟨s,hs,hp⟩ := hcorner
  have ht1 : paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a t)=paperQuadrilateralNextSide k := by
    by_cases he : s=t
    · simpa only [he] using hp
    · have hneq : paperAxisProperEndpointBoundaryCoordinate g hg a ha s ≠ paperAxisProperEndpointBoundaryCoordinate g hg a ha t :=
        fun hc => he (allCorner_boundary_eq_tag g hg a ha hproject s t k hs ht hc)
      exact (paperAxisCorner_source_nearer_partner g hg a ha hproject k s t hs hp ht
        (lt_of_le_of_ne (hmax s hs) hneq)).1
  by_contra he
  have hneq : paperAxisProperEndpointBoundaryCoordinate g hg a ha u ≠
      paperAxisProperEndpointBoundaryCoordinate g hg a ha (paperAxisProperArcEndpointPair g hg a t) := by
    intro hc
    exact he (allCorner_boundary_eq_tag g hg a ha hproject u _ _ hu ht1 hc).symm
  have hn := paperAxisCorner_next_nearer_partner g hg a ha hproject k t u ht ht1 hu
    (lt_of_le_of_ne (hmin _ ht1) hneq)
  exact not_lt_of_ge (hmax _ hn.1) hn.2

/-- The actual finite oriented side sorts construct the nearest pair in ALL
four corners. Nonempty ranks and extremal inequalities are derived internally
from actual complete lists; nearest matching is a theorem, never an input. -/
theorem paperAxisCorner_sorted_extrema_arc_paired
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn (fun r => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (k : Fin 4)
    (hcorner : ∃ s : paperAxisProperEndpointTag g hg a,
      paperAxisProperEndpointSide g hg a ha s=k ∧
        paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a s)=paperQuadrilateralNextSide k) :
    ∃ (h0 : 0<(paperAxisProperEndpointSideCoordinates g hg a ha k).card)
      (h1 : 0<(paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide k)).card),
      paperAxisProperArcEndpointPair g hg a
        (paperAxisProperEndpointBoundarySortedTag g hg a ha k
          ⟨(paperAxisProperEndpointSideCoordinates g hg a ha k).card-1,Nat.sub_lt h0 (by decide)⟩) =
        paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralNextSide k) ⟨0,h1⟩ := by
  classical
  have hpos (j : Fin 4) (t : paperAxisProperEndpointTag g hg a)
      (ht : paperAxisProperEndpointSide g hg a ha t=j) :
      0<(paperAxisProperEndpointSideCoordinates g hg a ha j).card := by
    have hm : t∈paperAxisProperEndpointSideTags g hg a ha j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩
    have hr : t∈Set.range (paperAxisProperEndpointBoundarySortedTag g hg a ha j) := by
      rw [paperAxisProperEndpointBoundarySortedTag_range g hg a ha hproject]
      exact hm
    obtain ⟨i,_⟩ := hr
    exact Nat.zero_lt_of_lt i.isLt
  obtain ⟨s,hs,hp⟩ := hcorner
  let h0 := hpos k s hs
  let h1 := hpos (paperQuadrilateralNextSide k) (paperAxisProperArcEndpointPair g hg a s) hp
  refine ⟨h0,h1,?_⟩
  apply paperAxisCorner_extrema_arc_paired g hg a ha hproject k
  · exact paperAxisProperEndpointBoundarySortedTag_side g hg a ha k _
  · exact paperAxisProperEndpointBoundarySortedTag_side g hg a ha (paperQuadrilateralNextSide k) _
  · intro v hv
    have hm : v∈paperAxisProperEndpointSideTags g hg a ha k := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
    have hr : v∈Set.range (paperAxisProperEndpointBoundarySortedTag g hg a ha k) := by
      rw [paperAxisProperEndpointBoundarySortedTag_range g hg a ha hproject]
      exact hm
    obtain ⟨i,rfl⟩ := hr
    apply (paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha k).monotone
    change i.val ≤ (paperAxisProperEndpointSideCoordinates g hg a ha k).card-1
    have := i.isLt
    omega
  · intro v hv
    have hm : v∈paperAxisProperEndpointSideTags g hg a ha (paperQuadrilateralNextSide k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
    have hr : v∈Set.range (paperAxisProperEndpointBoundarySortedTag g hg a ha (paperQuadrilateralNextSide k)) := by
      rw [paperAxisProperEndpointBoundarySortedTag_range g hg a ha hproject]
      exact hm
    obtain ⟨i,rfl⟩ := hr
    exact (paperAxisProperEndpointBoundarySortedTag_strictMono g hg a ha (paperQuadrilateralNextSide k)).monotone (Nat.zero_le _)
  · exact ⟨s,hs,hp⟩

end Markov
