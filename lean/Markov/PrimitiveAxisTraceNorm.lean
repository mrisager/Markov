import Markov.PaperAxisPrimitiveMissingCorner
import Markov.PaperAxisRoleZeroMechanicalWord
import Markov.PaperAxisRoleOneMechanicalWord
import Markov.MechanicalWordCanonicalConjugacy
import Markov.CanonicalWordConjugacyLengths

/-! Metric periods of primitive simple projected axes. The geometric
arc packets give signed mechanical words in both orientation cases. Their
conjugacy to the canonical words identifies the periods with the trace norm.
-/

noncomputable section
open Set
namespace Markov

/-- Every actual simple projected hyperbolic axis with primitive ORIGINAL
A/B H1 has the genuine trace-norm metric period. No canonical-class, missing
corner, packet, rotation, orientation or primitive-length premise is supplied. -/
theorem paperAxisPrimitive_period_eq_trace_norm
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (hp : IsCoprime (paperTraceAbelianizationCoordinates g).toAdd.1
      (paperTraceAbelianizationCoordinates g).toAdd.2) :
    modularClosedGeodesicPeriod g =
      ‖intVector traceBasis (paperTraceAbelianizationCoordinates g).toAdd‖ := by
  let w := paperAxisPeriodCellWord g hg a
  have hpw : IsCoprime ((w.map paperAxisCellLetterCoordinates).sum).1
      ((w.map paperAxisCellLetterCoordinates).sum).2 := by
    dsimp only [w]
    rw [paperAxisPeriodCellWord_signedSum g hg a ha]
    exact hp
  obtain ⟨k,hmissing⟩ := paperAxisPrimitive_exists_missing_previous_corner
    g hg a ha hproject hp
  rcases paperAxisMissingCorner_role0_word_or_role1 g hg a ha hproject k hmissing with h | h
  · obtain ⟨hpos,i,_,hword⟩ := h
    have hn : 0 <
        (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card +
        (paperAxisProperEndpointSideCoordinates g hg a ha k).card := by omega
    obtain ⟨hv,hcan⟩ := paperSideWord_forward_mechanical_rotation_isConj
      w i.val (paperQuadrilateralNextSide k) _ _ hn hword hpw
    exact modularClosedGeodesicPeriod_eq_trace_norm_of_cellWord_conjugacy
      g hg a ha (paperTraceAbelianizationCoordinates g).toAdd rfl
      (paperQuadrilateralNextSide k) (-((w.map paperAxisCellLetterCoordinates).sum)) hv
      (Or.inl hcan)
  · obtain ⟨hpos,i,_,hcycle⟩ := paperAxisCyclic_missing_corner_role1_word
      g hg a ha hproject k hmissing h
    have hn : 0 <
        (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card +
        (paperAxisProperEndpointSideCoordinates g hg a ha k).card := by omega
    have hword : ((w.rotate i.val).reverse.map paperQuadrilateralOppositeSide) =
        quadrantLowerMechanicalSideWord (paperQuadrilateralNextSide k)
          (paperAxisProperEndpointSideCoordinates g hg a ha (paperQuadrilateralNextSide.symm k)).card
          (paperAxisProperEndpointSideCoordinates g hg a ha k).card :=
      (paperAxisPrevSourceCycle_eq_reverse_rotate g hg a ha hproject i).symm.trans hcycle
    obtain ⟨hv,hcan⟩ := paperSideWord_backward_mechanical_rotation_isConj_inverse
      w i.val (paperQuadrilateralNextSide k) _ _ hn hword hpw
    exact modularClosedGeodesicPeriod_eq_trace_norm_of_cellWord_conjugacy
      g hg a ha (paperTraceAbelianizationCoordinates g).toAdd rfl
      (paperQuadrilateralNextSide k) ((w.map paperAxisCellLetterCoordinates).sum) hv
      (Or.inr hcan)

end Markov
