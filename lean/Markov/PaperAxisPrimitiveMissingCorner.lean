import Markov.PaperAxisPrimitiveCornerExclusion

/-! The actual primitive obstruction supplies a missing corner for the
all-side packet model. No missing-packet premise is supplied to this wrapper. -/

noncomputable section
open Set
namespace Markov

/-- Every actual primitive simple-period diagram has an actual literal side
whose previous-corner member count vanishes. This discharges the input of the
generic all-side state and orientation theorems without a classifying field. -/
theorem paperAxisPrimitive_exists_missing_previous_corner
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (hp : IsCoprime (paperTraceAbelianizationCoordinates g).toAdd.1
      (paperTraceAbelianizationCoordinates g).toAdd.2) :
    ∃ k : Fin 4, paperAxisProperArcPairCount g hg a ha k
      (paperQuadrilateralNextSide.symm k) = 0 := by
  rcases paperAxisProperArcSixCount_corner_zero_or_zero_of_primitive
    g hg a ha hproject hp with h0 | h1
  · refine ⟨1, ?_⟩
    change paperAxisProperArcPairCount g hg a ha 1 0 = 0
    rw [paperAxisProperArcPairCount_comm g hg a ha 1 0]
    exact h0
  · refine ⟨2, ?_⟩
    change paperAxisProperArcPairCount g hg a ha 2 1 = 0
    rw [paperAxisProperArcPairCount_comm g hg a ha 2 1]
    exact h1

end Markov
