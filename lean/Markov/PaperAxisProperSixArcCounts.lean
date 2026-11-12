import Markov.PaperAxisOppositeEndpointCounts
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Six counts are constructed from the ACTUAL proper-arc endpoint sides.
The actual tagged endpoint enumeration proves side-incidence formulas, and
the actual opposite-side bijection proves the two corner-count balances.
No count partition, balance, layer or classification field is assumed. -/
noncomputable section
open Set Topology
open scoped BigOperators
namespace Markov

/-- The two constructed endpoint-side labels of every actual arc differ. -/
theorem paperAxisProperArc_endpointSide_ne
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (i : paperAxisProperArcIndex g hg a) :
    paperAxisProperEndpointSide g hg a ha (i,0) ≠ paperAxisProperEndpointSide g hg a ha (i,1) := by
  obtain ⟨k,l,hkl,hk,hl,_,_⟩ := paperAxisProperArc_endpoint_sides g hg a ha i
  have hku : k = paperAxisProperEndpointSide g hg a ha (i,0) :=
    paperAxisProperEndpointSide_unique g hg a ha (i,0) k hk
  have hlu : l = paperAxisProperEndpointSide g hg a ha (i,1) :=
    paperAxisProperEndpointSide_unique g hg a ha (i,1) l hl
  intro he
  exact hkl (hku.trans (he.trans hlu.symm))

/-- Number of ACTUAL arc indices whose two actual endpoint sides are the
specified unordered pair; orientation is retained elsewhere, not guessed here. -/
def paperAxisProperArcPairCount
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k l : Fin 4) : ℕ := by
  classical
  exact Fintype.card {i : paperAxisProperArcIndex g hg a //
    (paperAxisProperEndpointSide g hg a ha (i,0) = k ∧
      paperAxisProperEndpointSide g hg a ha (i,1) = l) ∨
    (paperAxisProperEndpointSide g hg a ha (i,0) = l ∧
      paperAxisProperEndpointSide g hg a ha (i,1) = k)}

/-- The literal count is unchanged when the unordered pair is reversed. -/
theorem paperAxisProperArcPairCount_comm
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k l : Fin 4) :
    paperAxisProperArcPairCount g hg a ha k l = paperAxisProperArcPairCount g hg a ha l k := by
  classical
  unfold paperAxisProperArcPairCount
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv (Equiv.refl (paperAxisProperArcIndex g hg a))
  intro i
  exact or_comm

/-- Positive literal pair count supplies an ACTUAL member arc with those
endpoint sides, and every such actual arc contributes to the literal count. -/
theorem paperAxisProperArcPairCount_pos_iff
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k l : Fin 4) :
    0 < paperAxisProperArcPairCount g hg a ha k l ↔
      ∃ i : paperAxisProperArcIndex g hg a,
        (paperAxisProperEndpointSide g hg a ha (i,0) = k ∧
          paperAxisProperEndpointSide g hg a ha (i,1) = l) ∨
        (paperAxisProperEndpointSide g hg a ha (i,0) = l ∧
          paperAxisProperEndpointSide g hg a ha (i,1) = k) := by
  classical
  unfold paperAxisProperArcPairCount
  rw [Fintype.card_pos_iff]
  constructor
  · rintro ⟨⟨i,hi⟩⟩
    exact ⟨i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨⟨i,hi⟩⟩

private theorem actualSubtype_card_indicator {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] :
    Fintype.card {x : α // p x} = ∑ x : α, if p x then (1:ℕ) else 0 := by
  rw [Fintype.card_subtype]
  exact (Finset.sum_boole p Finset.univ).symm

private theorem actualPairCount_indicator
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k l : Fin 4) :
    paperAxisProperArcPairCount g hg a ha k l =
      ∑ i : paperAxisProperArcIndex g hg a,
        if (paperAxisProperEndpointSide g hg a ha (i,0) = k ∧
            paperAxisProperEndpointSide g hg a ha (i,1) = l) ∨
          (paperAxisProperEndpointSide g hg a ha (i,0) = l ∧
            paperAxisProperEndpointSide g hg a ha (i,1) = k) then 1 else 0 := by
  classical
  unfold paperAxisProperArcPairCount
  exact actualSubtype_card_indicator _

/-- There are no actual same-side arcs, proved from their actual endpoint data. -/
theorem paperAxisProperArcPairCount_self
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) :
    paperAxisProperArcPairCount g hg a ha k k = 0 := by
  classical
  rw [actualPairCount_indicator]
  apply Finset.sum_eq_zero
  intro i _
  have hn := paperAxisProperArc_endpointSide_ne g hg a ha i
  split_ifs with hp
  · rcases hp with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact (hn (hs.trans ht.symm)).elim
    · exact (hn (hs.trans ht.symm)).elim
  · rfl

/-- The six literal unoriented ACTUAL counts in order 01,12,23,30,02,13. -/
def paperAxisProperArcSixCount
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (r : Fin 6) : ℕ :=
  ![paperAxisProperArcPairCount g hg a ha 0 1,
    paperAxisProperArcPairCount g hg a ha 1 2,
    paperAxisProperArcPairCount g hg a ha 2 3,
    paperAxisProperArcPairCount g hg a ha 3 0,
    paperAxisProperArcPairCount g hg a ha 0 2,
    paperAxisProperArcPairCount g hg a ha 1 3] r

private theorem actualSideCount_indicator
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) :
    paperAxisProperEndpointSideCount g hg a ha k =
      ∑ i : paperAxisProperArcIndex g hg a,
        ((if paperAxisProperEndpointSide g hg a ha (i,0) = k then (1:ℕ) else 0) +
          (if paperAxisProperEndpointSide g hg a ha (i,1) = k then 1 else 0)) := by
  classical
  unfold paperAxisProperEndpointSideCount
  rw [actualSubtype_card_indicator]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  exact Fin.sum_univ_two _

private theorem actualIncidence_indicator (k x y : Fin 4) (hne : x ≠ y) :
    (if x = k then (1:ℕ) else 0) + (if y = k then 1 else 0) =
      ∑ l : Fin 4, if (x = k ∧ y = l) ∨ (x = l ∧ y = k) then 1 else 0 := by
  revert k x y
  decide

/-- Actual endpoint side counts equal incidence sums of ACTUAL unordered arc
counts, proved by enumerating each actual arc's two different endpoint tags. -/
theorem paperAxisProperEndpointSideCount_eq_pairSum
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) :
    paperAxisProperEndpointSideCount g hg a ha k =
      ∑ l : Fin 4, paperAxisProperArcPairCount g hg a ha k l := by
  classical
  rw [actualSideCount_indicator]
  simp_rw [actualPairCount_indicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact actualIncidence_indicator k _ _ (paperAxisProperArc_endpointSide_ne g hg a ha i)

/-- The four ACTUAL side totals are a+d+e, a+b+f, b+c+e, c+d+f for the six
ACTUAL arc counts [a,b,c,d,e,f]=[01,12,23,30,02,13]. -/
theorem paperAxisProperEndpointSideCount_six_formulas
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) :
    paperAxisProperEndpointSideCount g hg a ha 0 =
        paperAxisProperArcSixCount g hg a ha 0 + paperAxisProperArcSixCount g hg a ha 3 +
          paperAxisProperArcSixCount g hg a ha 4 ∧
    paperAxisProperEndpointSideCount g hg a ha 1 =
        paperAxisProperArcSixCount g hg a ha 0 + paperAxisProperArcSixCount g hg a ha 1 +
          paperAxisProperArcSixCount g hg a ha 5 ∧
    paperAxisProperEndpointSideCount g hg a ha 2 =
        paperAxisProperArcSixCount g hg a ha 1 + paperAxisProperArcSixCount g hg a ha 2 +
          paperAxisProperArcSixCount g hg a ha 4 ∧
    paperAxisProperEndpointSideCount g hg a ha 3 =
        paperAxisProperArcSixCount g hg a ha 2 + paperAxisProperArcSixCount g hg a ha 3 +
          paperAxisProperArcSixCount g hg a ha 5 := by
  have h0 := paperAxisProperEndpointSideCount_eq_pairSum g hg a ha 0
  have h1 := paperAxisProperEndpointSideCount_eq_pairSum g hg a ha 1
  have h2 := paperAxisProperEndpointSideCount_eq_pairSum g hg a ha 2
  have h3 := paperAxisProperEndpointSideCount_eq_pairSum g hg a ha 3
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at h0 h1 h2 h3
  change paperAxisProperEndpointSideCount g hg a ha 0 =
    paperAxisProperArcPairCount g hg a ha 0 0 +
      (paperAxisProperArcPairCount g hg a ha 0 1 +
        (paperAxisProperArcPairCount g hg a ha 0 2 + paperAxisProperArcPairCount g hg a ha 0 3)) at h0
  change paperAxisProperEndpointSideCount g hg a ha 1 =
    paperAxisProperArcPairCount g hg a ha 1 0 +
      (paperAxisProperArcPairCount g hg a ha 1 1 +
        (paperAxisProperArcPairCount g hg a ha 1 2 + paperAxisProperArcPairCount g hg a ha 1 3)) at h1
  change paperAxisProperEndpointSideCount g hg a ha 2 =
    paperAxisProperArcPairCount g hg a ha 2 0 +
      (paperAxisProperArcPairCount g hg a ha 2 1 +
        (paperAxisProperArcPairCount g hg a ha 2 2 + paperAxisProperArcPairCount g hg a ha 2 3)) at h2
  change paperAxisProperEndpointSideCount g hg a ha 3 =
    paperAxisProperArcPairCount g hg a ha 3 0 +
      (paperAxisProperArcPairCount g hg a ha 3 1 +
        (paperAxisProperArcPairCount g hg a ha 3 2 + paperAxisProperArcPairCount g hg a ha 3 3)) at h3
  rw [paperAxisProperArcPairCount_self] at h0 h1 h2 h3
  have h03 := paperAxisProperArcPairCount_comm g hg a ha 0 3
  have h10 := paperAxisProperArcPairCount_comm g hg a ha 1 0
  have h20 := paperAxisProperArcPairCount_comm g hg a ha 2 0
  have h21 := paperAxisProperArcPairCount_comm g hg a ha 2 1
  have h31 := paperAxisProperArcPairCount_comm g hg a ha 3 1
  have h32 := paperAxisProperArcPairCount_comm g hg a ha 3 2
  change paperAxisProperEndpointSideCount g hg a ha 0 =
      paperAxisProperArcPairCount g hg a ha 0 1 + paperAxisProperArcPairCount g hg a ha 3 0 +
        paperAxisProperArcPairCount g hg a ha 0 2 ∧
    paperAxisProperEndpointSideCount g hg a ha 1 =
      paperAxisProperArcPairCount g hg a ha 0 1 + paperAxisProperArcPairCount g hg a ha 1 2 +
        paperAxisProperArcPairCount g hg a ha 1 3 ∧
    paperAxisProperEndpointSideCount g hg a ha 2 =
      paperAxisProperArcPairCount g hg a ha 1 2 + paperAxisProperArcPairCount g hg a ha 2 3 +
        paperAxisProperArcPairCount g hg a ha 0 2 ∧
    paperAxisProperEndpointSideCount g hg a ha 3 =
      paperAxisProperArcPairCount g hg a ha 2 3 + paperAxisProperArcPairCount g hg a ha 3 0 +
        paperAxisProperArcPairCount g hg a ha 1 3
  omega

/-- The ACTUAL opposite endpoint bijection forces a=c and b=d for the
constructed six arc counts. No balancing/count data are assumed. -/
theorem paperAxisProperArcSixCount_corner_balance
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g))) :
    paperAxisProperArcSixCount g hg a ha 0 = paperAxisProperArcSixCount g hg a ha 2 ∧
      paperAxisProperArcSixCount g hg a ha 1 = paperAxisProperArcSixCount g hg a ha 3 := by
  have hf := paperAxisProperEndpointSideCount_six_formulas g hg a ha
  have h0 := paperAxisProperEndpointSideCount_eq_opposite g hg a ha hproject 0
  have h1 := paperAxisProperEndpointSideCount_eq_opposite g hg a ha hproject 1
  change paperAxisProperEndpointSideCount g hg a ha 0 = paperAxisProperEndpointSideCount g hg a ha 2 at h0
  change paperAxisProperEndpointSideCount g hg a ha 1 = paperAxisProperEndpointSideCount g hg a ha 3 at h1
  rw [hf.1,hf.2.2.1] at h0
  rw [hf.2.1,hf.2.2.2] at h1
  omega

end Markov
