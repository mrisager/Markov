import Markov.PaperQuadrilateralRawSideFrame
import Markov.PaperAxisProperSixArcCounts
import Markov.PaperAxisProperDiagramConnected
import Mathlib.Logic.Basic

/-! Actual all-side missing-corner orientation. A zero actual previous-corner
member count forces the opposite corner count to vanish by the proved balance.
The actual side bipartition and the literal endpoint roles are then linked by
genuine pairing connectedness. No orientation or component field is supplied. -/

noncomputable section
open Set
namespace Markov

private def missingCornerSide (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4)
    (t : paperAxisProperEndpointTag g hg a) : Prop :=
  paperAxisProperEndpointSide g hg a ha t = k ∨
    paperAxisProperEndpointSide g hg a ha t = paperQuadrilateralNextSide.symm k

private theorem missingCorner_count_opposite
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) (k : Fin 4) :
    paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide.symm k) =
      paperAxisProperArcPairCount g hg a ha (paperQuadrilateralOppositeSide k)
        (paperQuadrilateralOppositeSide (paperQuadrilateralNextSide.symm k)) := by
  have hb := paperAxisProperArcSixCount_corner_balance g hg a ha hproject
  change paperAxisProperArcPairCount g hg a ha 0 1 = paperAxisProperArcPairCount g hg a ha 2 3 ∧
    paperAxisProperArcPairCount g hg a ha 1 2 = paperAxisProperArcPairCount g hg a ha 3 0 at hb
  fin_cases k
  · change paperAxisProperArcPairCount g hg a ha 0 3 = paperAxisProperArcPairCount g hg a ha 2 1
    rw [paperAxisProperArcPairCount_comm g hg a ha 0 3,
      paperAxisProperArcPairCount_comm g hg a ha 2 1]
    exact hb.2.symm
  · change paperAxisProperArcPairCount g hg a ha 1 0 = paperAxisProperArcPairCount g hg a ha 3 2
    rw [paperAxisProperArcPairCount_comm g hg a ha 1 0,
      paperAxisProperArcPairCount_comm g hg a ha 3 2]
    exact hb.1
  · change paperAxisProperArcPairCount g hg a ha 2 1 = paperAxisProperArcPairCount g hg a ha 0 3
    rw [paperAxisProperArcPairCount_comm g hg a ha 2 1,
      paperAxisProperArcPairCount_comm g hg a ha 0 3]
    exact hb.2
  · change paperAxisProperArcPairCount g hg a ha 3 2 = paperAxisProperArcPairCount g hg a ha 1 0
    rw [paperAxisProperArcPairCount_comm g hg a ha 3 2,
      paperAxisProperArcPairCount_comm g hg a ha 1 0]
    exact hb.1.symm

private theorem missingCorner_zero_excludes_member
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k l : Fin 4)
    (hz : paperAxisProperArcPairCount g hg a ha k l = 0)
    (i : paperAxisProperArcIndex g hg a) :
    ¬ ((paperAxisProperEndpointSide g hg a ha (i, 0) = k ∧
          paperAxisProperEndpointSide g hg a ha (i, 1) = l) ∨
        (paperAxisProperEndpointSide g hg a ha (i, 0) = l ∧
          paperAxisProperEndpointSide g hg a ha (i, 1) = k)) := by
  intro h
  have hp := (paperAxisProperArcPairCount_pos_iff g hg a ha k l).mpr ⟨i, h⟩
  omega

private theorem missingCorner_arc_flips_side
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) (k : Fin 4)
    (hmissing : paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide.symm k) = 0)
    (t : paperAxisProperEndpointTag g hg a) :
    missingCornerSide g hg a ha k (paperAxisProperArcEndpointPair g hg a t) ↔
      ¬ missingCornerSide g hg a ha k t := by
  have hz : paperAxisProperArcPairCount g hg a ha (paperQuadrilateralOppositeSide k)
      (paperQuadrilateralOppositeSide (paperQuadrilateralNextSide.symm k)) = 0 :=
    (missingCorner_count_opposite g hg a ha hproject k).symm.trans hmissing
  have hbase (i : paperAxisProperArcIndex g hg a) :
      missingCornerSide g hg a ha k (i, 1) ↔ ¬ missingCornerSide g hg a ha k (i, 0) := by
    have hn := paperAxisProperArc_endpointSide_ne g hg a ha i
    have h0 := missingCorner_zero_excludes_member g hg a ha k
      (paperQuadrilateralNextSide.symm k) hmissing i
    have h1 := missingCorner_zero_excludes_member g hg a ha (paperQuadrilateralOppositeSide k)
      (paperQuadrilateralOppositeSide (paperQuadrilateralNextSide.symm k)) hz i
    unfold missingCornerSide
    generalize hs : paperAxisProperEndpointSide g hg a ha (i, 0) = s at hn h0 h1 ⊢
    generalize ht : paperAxisProperEndpointSide g hg a ha (i, 1) = u at hn h0 h1 ⊢
    fin_cases k <;> fin_cases s <;> fin_cases u <;>
      simp_all [paperQuadrilateralNextSide, paperQuadrilateralOppositeSide]
  rcases t with ⟨i, e⟩
  fin_cases e
  · exact hbase i
  · change missingCornerSide g hg a ha k (i, 0) ↔ ¬ missingCornerSide g hg a ha k (i, 1)
    exact iff_not_comm.mp (hbase i)

private theorem missingCorner_edge_flips_side
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) (k : Fin 4)
    (t : paperAxisProperEndpointTag g hg a) :
    missingCornerSide g hg a ha k (paperAxisProperEdgePair g hg a t) ↔
      ¬ missingCornerSide g hg a ha k t := by
  unfold missingCornerSide
  rw [(paperAxisProperEdgePair_opposite_and_coordinate g hg a ha hproject t).1]
  generalize paperAxisProperEndpointSide g hg a ha t = s
  fin_cases k <;> fin_cases s <;> decide

private theorem missingCorner_arc_flips_role
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (t : paperAxisProperEndpointTag g hg a) :
    (paperAxisProperArcEndpointPair g hg a t).2 = 0 ↔ ¬ t.2 = 0 := by
  rcases t with ⟨i, e⟩
  fin_cases e
  · change (1 : Fin 2) = 0 ↔ ¬ (0 : Fin 2) = 0
    decide
  · change (0 : Fin 2) = 0 ↔ ¬ (1 : Fin 2) = 0
    decide

private theorem missingCorner_edge_flips_role
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (t : paperAxisProperEndpointTag g hg a) :
    (paperAxisProperEdgePair g hg a t).2 = 0 ↔ ¬ t.2 = 0 := by
  rcases t with ⟨i, e⟩
  fin_cases e
  · change (1 : Fin 2) = 0 ↔ ¬ (0 : Fin 2) = 0
    decide
  · change (0 : Fin 2) = 0 ↔ ¬ (1 : Fin 2) = 0
    decide

/-- For EVERY literal side k, a missing actual previous-corner arc forces
the actual adjacent-side subset to be exactly all sources or all targets.
The actual connected diagram, not an orientation field, proves the choice. -/
theorem paperAxisMissingCorner_side_role_partition
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) (k : Fin 4)
    (hmissing : paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide.symm k) = 0) :
    (∀ t : paperAxisProperEndpointTag g hg a,
      (paperAxisProperEndpointSide g hg a ha t = k ∨
        paperAxisProperEndpointSide g hg a ha t = paperQuadrilateralNextSide.symm k) ↔ t.2 = 0) ∨
    (∀ t : paperAxisProperEndpointTag g hg a,
      (paperAxisProperEndpointSide g hg a ha t = k ∨
        paperAxisProperEndpointSide g hg a ha t = paperQuadrilateralNextSide.symm k) ↔ t.2 = 1) := by
  classical
  let P (t : paperAxisProperEndpointTag g hg a) := missingCornerSide g hg a ha k t ↔ t.2 = 0
  have hArc (t : paperAxisProperEndpointTag g hg a) :
      P (paperAxisProperArcEndpointPair g hg a t) ↔ P t := by
    dsimp only [P]
    rw [missingCorner_arc_flips_side g hg a ha hproject k hmissing, missingCorner_arc_flips_role]
    exact not_iff_not
  have hEdge (t : paperAxisProperEndpointTag g hg a) :
      P (paperAxisProperEdgePair g hg a t) ↔ P t := by
    dsimp only [P]
    rw [missingCorner_edge_flips_side g hg a ha hproject k, missingCorner_edge_flips_role]
    exact not_iff_not
  have hstep {t u : paperAxisProperEndpointTag g hg a}
      (hs : paperAxisProperEndpointStep g hg a t u) : P t ↔ P u := by
    rcases hs with rfl | rfl
    · exact (hArc t).symm
    · exact (hEdge t).symm
  have hwalk {t u : paperAxisProperEndpointTag g hg a}
      (hw : Relation.ReflTransGen (paperAxisProperEndpointStep g hg a) t u) : P t ↔ P u := by
    induction hw with
    | refl => rfl
    | tail hw hs ih => exact ih.trans (hstep hs)
  have hc := paperAxisPeriodCutPoints_three_le_of_off_sides g hg a ha
  let t₀ : paperAxisProperEndpointTag g hg a := (⟨0, by omega⟩, 0)
  by_cases h0 : missingCornerSide g hg a ha k t₀
  · left
    have hp : P t₀ := ⟨fun _ => rfl, fun _ => h0⟩
    intro t
    exact (hwalk (paperAxisProperEndpoint_pairings_connected g hg a t₀ t)).mp hp
  · right
    have hp : ¬ P t₀ := by
      intro hh
      exact h0 (hh.mpr rfl)
    intro t
    have hn : ¬ P t := fun hh => hp
      ((hwalk (paperAxisProperEndpoint_pairings_connected g hg a t₀ t)).mpr hh)
    have hrole : t.2 = 1 ↔ ¬ t.2 = 0 := by
      rcases t with ⟨i, e⟩
      fin_cases e
      · change (0 : Fin 2) = 1 ↔ ¬ (0 : Fin 2) = 0
        decide
      · change (1 : Fin 2) = 1 ↔ ¬ (1 : Fin 2) = 0
        decide
    change missingCornerSide g hg a ha k t ↔ t.2 = 1
    rw [hrole]
    dsimp only [P] at hn
    exact (not_iff_comm.mp (not_iff.mp hn)).symm

/-- All actual sources belong to one of the two complementary actual side
blocks, under ONLY the genuine missing previous-corner member count. -/
theorem paperAxisMissingCorner_source_side_partition
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) (k : Fin 4)
    (hmissing : paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide.symm k) = 0) :
    (∀ i : paperAxisProperArcIndex g hg a,
      paperAxisProperEndpointSide g hg a ha (i, 0) = k ∨
        paperAxisProperEndpointSide g hg a ha (i, 0) = paperQuadrilateralNextSide.symm k) ∨
    (∀ i : paperAxisProperArcIndex g hg a,
      paperAxisProperEndpointSide g hg a ha (i, 0) = paperQuadrilateralNextSide k ∨
        paperAxisProperEndpointSide g hg a ha (i, 0) = paperQuadrilateralOppositeSide k) := by
  rcases paperAxisMissingCorner_side_role_partition g hg a ha hproject k hmissing with h | h
  · exact Or.inl (fun i => (h (i, 0)).mpr rfl)
  · right
    intro i
    have hn : ¬ (paperAxisProperEndpointSide g hg a ha (i, 0) = k ∨
        paperAxisProperEndpointSide g hg a ha (i, 0) = paperQuadrilateralNextSide.symm k) := by
      intro hs
      have he := (h (i, 0)).mp hs
      exact (show (0 : Fin 2) ≠ 1 by decide) he
    generalize paperAxisProperEndpointSide g hg a ha (i, 0) = s at hn ⊢
    fin_cases k <;> fin_cases s <;>
      simp_all [paperQuadrilateralNextSide, paperQuadrilateralOppositeSide]

/-- The same actual orientation alternative as literal equality of actual
tag subsets, ready to combine with any proved actual state-table range. -/
theorem paperAxisMissingCorner_side_set_eq_role_set
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) (k : Fin 4)
    (hmissing : paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide.symm k) = 0) :
    {t : paperAxisProperEndpointTag g hg a | paperAxisProperEndpointSide g hg a ha t = k ∨
        paperAxisProperEndpointSide g hg a ha t = paperQuadrilateralNextSide.symm k} = {t | t.2 = 0} ∨
    {t : paperAxisProperEndpointTag g hg a | paperAxisProperEndpointSide g hg a ha t = k ∨
        paperAxisProperEndpointSide g hg a ha t = paperQuadrilateralNextSide.symm k} = {t | t.2 = 1} := by
  rcases paperAxisMissingCorner_side_role_partition g hg a ha hproject k hmissing with h | h
  · exact Or.inl (Set.ext h)
  · exact Or.inr (Set.ext h)

end Markov
