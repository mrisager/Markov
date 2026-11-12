import Markov.SingularHomotopyBoundary
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-! Explicit actual two-boundaries for reversal and connecting-path loop
closure. These are chain equalities, not a homology-generation premise. -/

noncomputable section
namespace Markov

variable (X : Type) [TopologicalSpace X]

/-- An actual two-chain whose boundary is a path plus its reversal. -/
def singularReversalTwoChain {a b : X} (γ : Path a b) :
    (integralSingularChainComplex X).X 2 :=
  singularConcatTriangleChain X γ γ.symm -
    singularHomotopyDifferenceChain X (Classical.choice (Path.Homotopic.trans_symm γ)) +
      singularConstantTwoChain X a

theorem singularReversalTwoChain_boundary {a b : X} (γ : Path a b) :
    (integralSingularChainComplex X).d 2 1 (singularReversalTwoChain X γ) =
      singularPathChain X γ + singularPathChain X γ.symm := by
  rw [singularReversalTwoChain, map_add, map_sub,
    singularConcatTriangleChain_boundary, singularHomotopyDifferenceChain_boundary,
    singularConstantTwoChain_boundary]
  abel

/-- Closing an edge with two connecting paths differs from the original edge
and the connecting-path correction by this explicit actual two-boundary. -/
def singularBasedLoopTwoChain {x a b : X} (α : Path x a) (γ : Path a b)
    (β : Path x b) : (integralSingularChainComplex X).X 2 :=
  singularReversalTwoChain X β - singularConcatTriangleChain X α γ -
    singularConcatTriangleChain X (α.trans γ) β.symm

theorem singularBasedLoopTwoChain_boundary {x a b : X} (α : Path x a)
    (γ : Path a b) (β : Path x b) :
    (integralSingularChainComplex X).d 2 1 (singularBasedLoopTwoChain X α γ β) =
      singularPathChain X ((α.trans γ).trans β.symm) - singularPathChain X γ -
        singularPathChain X α + singularPathChain X β := by
  rw [singularBasedLoopTwoChain, map_sub, map_sub,
    singularReversalTwoChain_boundary, singularConcatTriangleChain_boundary,
    singularConcatTriangleChain_boundary]
  abel

end Markov
