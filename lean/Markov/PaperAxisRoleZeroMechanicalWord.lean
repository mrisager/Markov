import Markov.PaperAxisMissingCornerOrientation
import Markov.PaperAxisCyclicPacketRotation
import Markov.PaperAxisSourceCycleWord
import Markov.MechanicalRotationCoding
import Markov.MechanicalCanonicalWords

/-! The ACTUAL role-zero source component gives the explicit signed mechanical
word. Its state table has the genuine actual word length by a constructed finite
bijection. Literal state0 anchors the actual source cycle and the checked actual
rotation/letter formulas prove the word equality. No mechanical normal form,
orientation, coprimality or class-equivalence field is supplied. -/

noncomputable section
open Set
namespace Markov

/-- A computed actual state table enumerating one literal role has exactly
one state per actual family member, proved by its actual tag injection and
the literal range equality. Both source and target roles are allowed here. -/
theorem paperAxisCyclic_state_role_count
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) (k : Fin 4) (e : Fin 2)
    (hRange : Set.range (paperAxisCyclicRankStateTag g hg a ha k) = {t | t.2 = e}) :
    (paperAxisProperEndpointSideCoordinates g hg a ha k).card +
      (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card =
        (paperAxisPeriodCellWord g hg a).length := by
  classical
  let M := (paperAxisProperEndpointSideCoordinates g hg a ha k).card +
    (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card
  let σ : Fin M → paperAxisProperEndpointTag g hg a := paperAxisCyclicRankStateTag g hg a ha k
  have hrole (r : Fin M) : (σ r).2 = e := by
    have hm : σ r ∈ Set.range (paperAxisCyclicRankStateTag g hg a ha k) := ⟨r, rfl⟩
    rw [hRange] at hm
    exact hm
  have hinj : Function.Injective (fun r : Fin M => (σ r).1) := by
    intro r s he
    apply paperAxisCyclicRankStateTag_injective g hg a ha k
    exact Prod.ext he ((hrole r).trans (hrole s).symm)
  have hsurj : Function.Surjective (fun r : Fin M => (σ r).1) := by
    intro i
    have hm : (i, e) ∈ Set.range (paperAxisCyclicRankStateTag g hg a ha k) := by
      rw [hRange]
      rfl
    obtain ⟨r, hr⟩ := hm
    exact ⟨r, congrArg Prod.fst hr⟩
  have hc := Fintype.card_congr (Equiv.ofBijective (fun r : Fin M => (σ r).1) ⟨hinj, hsurj⟩)
  rw [paperAxisPeriodCellWord_length]
  simpa only [Fintype.card_fin] using hc

/-- In the ACTUAL source-role branch, an actual source index anchored at
literal state0 reads the actual side word as the EXPLICIT signed mechanical
list [NextSide k,Opposite k]. Its sizes are genuine actual side cardinalities;
no word-identity, normal-form or primitive/H1 premise is an input. -/
theorem paperAxisCyclic_missing_corner_role0_word
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) (k : Fin 4)
    (hmissing : paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide.symm k) = 0)
    (hRange : Set.range (paperAxisCyclicRankStateTag g hg a ha k) = {t | t.2 = 0}) :
    ∃ (hpos : 0 < (paperAxisProperEndpointSideCoordinates g hg a ha k).card +
          (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card)
      (i₀ : paperAxisProperArcIndex g hg a),
      paperAxisCyclicRankStateTag g hg a ha k ⟨0, hpos⟩ = (i₀, 0) ∧
      (paperAxisPeriodCellWord g hg a).rotate i₀.val =
        quadrantLowerMechanicalSideWord (paperQuadrilateralNextSide k)
          (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card
          (paperAxisProperEndpointSideCoordinates g hg a ha k).card := by
  classical
  let N := (paperAxisProperEndpointSideCoordinates g hg a ha k).card
  let P := (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card
  let M := N + P
  let σ : Fin M → paperAxisProperEndpointTag g hg a := paperAxisCyclicRankStateTag g hg a ha k
  have hmass : M = (paperAxisPeriodCellWord g hg a).length :=
    paperAxisCyclic_state_role_count g hg a ha k 0 hRange
  have hwordpos : 0 < (paperAxisPeriodCellWord g hg a).length := by
    rw [paperAxisPeriodCellWord_length]
    have hc := paperAxisPeriodCutPoints_three_le_of_off_sides g hg a ha
    omega
  have hpos : 0 < M := by omega
  let z : Fin M := ⟨0, hpos⟩
  let i₀ := (σ z).1
  have hrole (r : Fin M) : (σ r).2 = 0 := by
    have hm : σ r ∈ Set.range (paperAxisCyclicRankStateTag g hg a ha k) := ⟨r, rfl⟩
    rw [hRange] at hm
    exact hm
  have hstart : σ z = (i₀, 0) := Prod.ext rfl (hrole z)
  let r (j : ℕ) : Fin M := ⟨(j * N) % M, Nat.mod_lt _ hpos⟩
  have hiter (j : ℕ) : σ (r j) = (((paperAxisProperArcNextIndex g hg a)^[j]) i₀, 0) := by
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
      rw [ih, paperAxisProperEndpointTraversal_source_next, hi] at hs
      simpa only [Function.iterate_succ_apply'] using hs.symm
  have hletter (j : ℕ) :
      paperAxisProperEndpointSide g hg a ha (((paperAxisProperArcNextIndex g hg a)^[j]) i₀, 1) =
        if (j * N) % M < P then paperQuadrilateralNextSide k else paperQuadrilateralOppositeSide k := by
    have hs := paperAxisCyclic_missing_corner_actual_letter g hg a ha hproject k hmissing (r j)
    change paperAxisProperEndpointSide g hg a ha (paperAxisProperArcEndpointPair g hg a (σ (r j))) =
      if (r j).val < P then paperQuadrilateralNextSide k else paperQuadrilateralOppositeSide k at hs
    rw [hiter j] at hs
    exact hs
  change ∃ (hpos : 0 < M) (i₀ : paperAxisProperArcIndex g hg a),
    σ ⟨0, hpos⟩ = (i₀, 0) ∧ (paperAxisPeriodCellWord g hg a).rotate i₀.val =
      quadrantLowerMechanicalSideWord (paperQuadrilateralNextSide k) P N
  refine ⟨hpos, i₀, hstart, ?_⟩
  rw [paperAxisPeriodCellWord_rotate_eq_sourceCycle g hg a ha i₀]
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

/-- Actual missing-corner geometry supplies either the PROVED role-zero
mechanical word identity or the literal target-role branch for the separately
owned reverse-orientation comparator. No preferred orientation is assumed. -/
theorem paperAxisMissingCorner_role0_word_or_role1
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b + modularClosedGeodesicPeriod g))) (k : Fin 4)
    (hmissing : paperAxisProperArcPairCount g hg a ha k (paperQuadrilateralNextSide.symm k) = 0) :
    (∃ (hpos : 0 < (paperAxisProperEndpointSideCoordinates g hg a ha k).card +
          (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card)
      (i₀ : paperAxisProperArcIndex g hg a),
      paperAxisCyclicRankStateTag g hg a ha k ⟨0, hpos⟩ = (i₀, 0) ∧
      (paperAxisPeriodCellWord g hg a).rotate i₀.val =
        quadrantLowerMechanicalSideWord (paperQuadrilateralNextSide k)
          (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card
          (paperAxisProperEndpointSideCoordinates g hg a ha k).card) ∨
      Set.range (paperAxisCyclicRankStateTag g hg a ha k) = {t | t.2 = 1} := by
  rcases paperAxisMissingCorner_side_set_eq_role_set g hg a ha hproject k hmissing with h | h
  · left
    apply paperAxisCyclic_missing_corner_role0_word g hg a ha hproject k hmissing
    rw [paperAxisCyclicRankStateTag_range g hg a ha k hproject]
    exact h
  · right
    rw [paperAxisCyclicRankStateTag_range g hg a ha k hproject]
    exact h

end Markov
