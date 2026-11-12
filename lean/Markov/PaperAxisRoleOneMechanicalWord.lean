import Markov.PaperAxisRoleZeroMechanicalWord
import Markov.PaperAxisBackwardCycleWord

/-! Actual role-one rotation coding. The literal EDGE-after-ARC traversal is
Prev on target roles. The actual state table therefore codes the actual
backwards-source word, whose inverse-conjugate product is checked separately.
No H1-to-class inference or canonical reversal identity is assumed. -/
noncomputable section
open Set
namespace Markov

/-- Literal target-role traversal is the actual predecessor cycle. -/
theorem paperAxisProperEndpointTraversal_target_prev
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : paperAxisProperArcIndex g hg a) :
    paperAxisProperEdgePair g hg a (paperAxisProperArcEndpointPair g hg a (i,1)) =
      (paperAxisProperArcPrevIndex g hg a i,1) := rfl

/-- The actual role-one state component reads the literal backwards-source
cycle as the explicitly signed mechanical list, anchored at actual state0. -/
theorem paperAxisCyclic_missing_corner_role1_word
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) (k : Fin 4)
    (hmissing : paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide.symm k) = 0)
    (hRange : Set.range (paperAxisCyclicRankStateTag g hg a ha k) = {t | t.2 = 1}) :
    ∃ (hpos : 0 < (paperAxisProperEndpointSideCoordinates g hg a ha k).card +
          (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card)
      (i₀ : paperAxisProperArcIndex g hg a),
      paperAxisCyclicRankStateTag g hg a ha k ⟨0, hpos⟩ = (i₀, 1) ∧
      List.ofFn (fun j : paperAxisProperArcIndex g hg a =>
        paperAxisProperEndpointSide g hg a ha
          (((paperAxisProperArcPrevIndex g hg a)^[j.val]) i₀,0)) =
        quadrantLowerMechanicalSideWord (paperQuadrilateralNextSide k)
          (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card
          (paperAxisProperEndpointSideCoordinates g hg a ha k).card := by
  classical
  let N := (paperAxisProperEndpointSideCoordinates g hg a ha k).card
  let P := (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card
  let M := N + P
  let σ : Fin M → paperAxisProperEndpointTag g hg a := paperAxisCyclicRankStateTag g hg a ha k
  have hmass : M = (paperAxisPeriodCellWord g hg a).length :=
    paperAxisCyclic_state_role_count g hg a ha k 1 hRange
  have hwordpos : 0 < (paperAxisPeriodCellWord g hg a).length := by
    rw [paperAxisPeriodCellWord_length]
    have hc := paperAxisPeriodCutPoints_three_le_of_off_sides g hg a ha
    omega
  have hpos : 0 < M := by omega
  let z : Fin M := ⟨0, hpos⟩
  let i₀ := (σ z).1
  have hrole (r : Fin M) : (σ r).2 = 1 := by
    have hm : σ r ∈ Set.range (paperAxisCyclicRankStateTag g hg a ha k) := ⟨r, rfl⟩
    rw [hRange] at hm
    exact hm
  have hstart : σ z = (i₀, 1) := Prod.ext rfl (hrole z)
  let r (j : ℕ) : Fin M := ⟨(j * N) % M, Nat.mod_lt _ hpos⟩
  have hiter (j : ℕ) : σ (r j) = (((paperAxisProperArcPrevIndex g hg a)^[j]) i₀, 1) := by
    induction j with
    | zero =>
      have hr : r 0 = z := by apply Fin.ext; simp only [r, z, Nat.zero_mul, Nat.zero_mod]
      simpa only [Function.iterate_zero_apply, hr] using hstart
    | succ j ih =>
      have hi : (⟨((r j).val + N) % M, Nat.mod_lt _ hpos⟩ : Fin M) = r (j + 1) := by
        apply Fin.ext
        dsimp only [r]
        rw [Nat.mod_add_mod]
        congr 1
        ring
      have hs := paperAxisCyclic_missing_corner_actual_rotation g hg a ha hproject k hmissing (r j)
      change paperAxisProperEdgePair g hg a (paperAxisProperArcEndpointPair g hg a (σ (r j))) =
        σ (⟨((r j).val + N) % M, Nat.mod_lt _ hpos⟩ : Fin M) at hs
      rw [ih, paperAxisProperEndpointTraversal_target_prev, hi] at hs
      simpa only [Function.iterate_succ_apply'] using hs.symm
  have hletter (j : ℕ) :
      paperAxisProperEndpointSide g hg a ha (((paperAxisProperArcPrevIndex g hg a)^[j]) i₀, 0) =
        if (j * N) % M < P then paperQuadrilateralNextSide k else paperQuadrilateralOppositeSide k := by
    have hs := paperAxisCyclic_missing_corner_actual_letter g hg a ha hproject k hmissing (r j)
    change paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a (σ (r j))) =
      if (r j).val < P then paperQuadrilateralNextSide k else paperQuadrilateralOppositeSide k at hs
    rw [hiter j] at hs
    exact hs
  change ∃ (hpos : 0 < M) (i₀ : paperAxisProperArcIndex g hg a),
    σ ⟨0, hpos⟩ = (i₀, 1) ∧ List.ofFn (fun j : paperAxisProperArcIndex g hg a =>
        paperAxisProperEndpointSide g hg a ha
          (((paperAxisProperArcPrevIndex g hg a)^[j.val]) i₀,0)) =
      quadrantLowerMechanicalSideWord (paperQuadrilateralNextSide k) P N
  refine ⟨hpos, i₀, hstart, ?_⟩
  apply List.ext_getElem
  · simp only [List.length_ofFn, quadrantLowerMechanicalSideWord,
      List.length_map, lowerMechanicalWord_length]
    rw [paperAxisPeriodCellWord_length] at hmass
    omega
  · intro j hj hm
    rw [List.getElem_ofFn, hletter j]
    simp only [quadrantLowerMechanicalSideWord, List.getElem_map,
      lowerMechanicalWord, List.getElem_range]
    rw [lowerMechanicalLetter_mod P N j (by dsimp [M] at hpos; omega),
      show P + N = M by dsimp [M]; omega, paperQuadrilateralNextSide_apply_twice]
    by_cases h : (j * N) % M < P
    · simp [h, show ¬ P ≤ (j * N) % M by omega]
    · simp [h, show P ≤ (j * N) % M by omega]

/-- The same geometric word identity in the direct reverse-of-forward-
rotation convention used by the checked nonabelian mechanical comparator. -/
theorem paperAxisCyclic_missing_corner_role1_reverse_word
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) (k : Fin 4)
    (hmissing : paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide.symm k) = 0)
    (hRange : Set.range (paperAxisCyclicRankStateTag g hg a ha k) = {t | t.2 = 1}) :
    ∃ (hpos : 0 < (paperAxisProperEndpointSideCoordinates g hg a ha k).card +
          (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card)
      (i₀ : paperAxisProperArcIndex g hg a),
      paperAxisCyclicRankStateTag g hg a ha k ⟨0,hpos⟩ = (i₀,1) ∧
      ((paperAxisPeriodCellWord g hg a).rotate i₀.val).reverse.map paperQuadrilateralOppositeSide =
        quadrantLowerMechanicalSideWord (paperQuadrilateralNextSide k)
          (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card
          (paperAxisProperEndpointSideCoordinates g hg a ha k).card := by
  obtain ⟨hpos,i₀,hstart,hword⟩ :=
    paperAxisCyclic_missing_corner_role1_word g hg a ha hproject k hmissing hRange
  exact ⟨hpos,i₀,hstart,(paperAxisPrevSourceCycle_eq_reverse_rotate g hg a ha hproject i₀).symm.trans hword⟩

/-- The same actual mechanical list evaluates to the explicit inverse
conjugate of the actual forward word product. The actual backwards comparator
fixes both traversal order and its one-step phase. -/
theorem paperAxisCyclic_missing_corner_role1_word_prod
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) (k : Fin 4)
    (hmissing : paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide.symm k) = 0)
    (hRange : Set.range (paperAxisCyclicRankStateTag g hg a ha k) = {t | t.2 = 1}) :
    ∃ (hpos : 0 < (paperAxisProperEndpointSideCoordinates g hg a ha k).card +
          (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card)
      (i₀ : paperAxisProperArcIndex g hg a),
      paperAxisCyclicRankStateTag g hg a ha k ⟨0,hpos⟩ = (i₀,1) ∧
      ((quadrantLowerMechanicalSideWord (paperQuadrilateralNextSide k)
          (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card
          (paperAxisProperEndpointSideCoordinates g hg a ha k).card).map paperQuadrilateralSideNeighbor).prod =
        (((paperAxisPeriodCellWord g hg a).take i₀.val).map paperQuadrilateralSideNeighbor).prod⁻¹ *
          ((paperAxisPeriodCellWord g hg a).map paperQuadrilateralSideNeighbor).prod⁻¹ *
        (((paperAxisPeriodCellWord g hg a).take i₀.val).map paperQuadrilateralSideNeighbor).prod := by
  obtain ⟨hpos,i₀,hstart,hword⟩ :=
    paperAxisCyclic_missing_corner_role1_word g hg a ha hproject k hmissing hRange
  refine ⟨hpos,i₀,hstart,?_⟩
  rw [← hword]
  exact paperAxisPrevSourceCycle_neighbor_prod g hg a ha hproject i₀

end Markov
