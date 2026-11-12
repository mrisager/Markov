import Markov.PaperQuadrilateralFiniteCover
import Markov.PaperQuadrilateralCutWords

noncomputable section
open scoped MatrixGroups
namespace Markov

def paperQuadrilateralCoverWordAt : Fin 10 → SL(2, ℤ) :=
  ![1, ModularGroup.T, ModularGroup.T⁻¹, ModularGroup.T * ModularGroup.S,
    ModularGroup.T⁻¹ * ModularGroup.S, ModularGroup.S, ModularGroup.S * ModularGroup.T,
    ModularGroup.S * ModularGroup.T⁻¹, ModularGroup.S * ModularGroup.T * ModularGroup.S,
    ModularGroup.S * ModularGroup.T⁻¹ * ModularGroup.S]

def paperQuadrilateralCoverResidue : Fin 10 → Fin 6 := ![0,1,5,4,2,3,4,2,1,5]

def paperQuadrilateralReturnCandidateAt : Fin 9 → SL(2, ℤ) :=
  ![1, paperGeneratorASL, paperGeneratorASL⁻¹, paperGeneratorBSL, paperGeneratorBSL⁻¹,
    ModularGroup.T ^ 3 * ModularGroup.S, (ModularGroup.T⁻¹) ^ 3 * ModularGroup.S,
    ModularGroup.S * ModularGroup.T ^ 3, ModularGroup.S * (ModularGroup.T⁻¹) ^ 3]

local instance : DecidableEq SL(2, ℤ) := fun a b =>
  decidable_of_iff (∀ i j : Fin 2, a i j = b i j) (Matrix.SpecialLinearGroup.ext_iff a b).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem paperQuadrilateralReturn_finite_enumeration :
    ∀ i j k : Fin 10,
      ((paperQuadrilateralCoverResidue j).val + (modularClosedReturnResidue k).val) % 6 =
        (paperQuadrilateralCoverResidue i).val →
      ∃ l : Fin 9,
        paperQuadrilateralCoverWordAt j * modularClosedReturnWordAt k *
          (paperQuadrilateralCoverWordAt i)⁻¹ = paperQuadrilateralReturnCandidateAt l ∨
        paperQuadrilateralCoverWordAt j * modularClosedReturnWordAt k *
          (paperQuadrilateralCoverWordAt i)⁻¹ = -paperQuadrilateralReturnCandidateAt l := by
  decide

end Markov
