import Markov.SingularOneChains
import Markov.PathHomotopyTriangles

/-! Actual integral singular two-chain boundaries for relative path homotopies.
These are equalities in the pinned singular chain complex, not assumed homology
relations or a Hurewicz identification. -/

open CategoryTheory

noncomputable section
namespace Markov

variable (X : Type) [TopologicalSpace X] {a b : X} {γ δ : Path a b}

def singularHomotopyLowerChain (F : Path.Homotopy γ δ) :
    (integralSingularChainComplex X).X 2 :=
  singularSimplexChain X (singularSimplexOfMap X (pathHomotopyLowerTriangle F))

def singularHomotopyUpperChain (F : Path.Homotopy γ δ) :
    (integralSingularChainComplex X).X 2 :=
  singularSimplexChain X (singularSimplexOfMap X (pathHomotopyUpperTriangle F))

theorem singularHomotopyLowerChain_boundary (F : Path.Homotopy γ δ) :
    (integralSingularChainComplex X).d 2 1 (singularHomotopyLowerChain X F) =
      singularPathChain X δ - singularPathChain X (pathHomotopyDiagonal F) +
        singularPathChain X (Path.refl a) := by
  rw [singularHomotopyLowerChain, singularSimplexChain_boundary_two]
  simp only [singularSimplexOfMap_face]
  change singularSimplexChain X (singularSimplexOfMap X
      ((pathHomotopyLowerTriangle F).comp (triangleFaceMap 0))) -
    singularSimplexChain X (singularSimplexOfMap X
      ((pathHomotopyLowerTriangle F).comp (triangleFaceMap 1))) +
    singularSimplexChain X (singularSimplexOfMap X
      ((pathHomotopyLowerTriangle F).comp (triangleFaceMap 2))) = _
  rw [pathHomotopyLowerTriangle_face_zero, pathHomotopyLowerTriangle_face_one,
    pathHomotopyLowerTriangle_face_two]
  rfl

theorem singularHomotopyUpperChain_boundary (F : Path.Homotopy γ δ) :
    (integralSingularChainComplex X).d 2 1 (singularHomotopyUpperChain X F) =
      singularPathChain X (Path.refl b) - singularPathChain X (pathHomotopyDiagonal F) +
        singularPathChain X γ := by
  rw [singularHomotopyUpperChain, singularSimplexChain_boundary_two]
  simp only [singularSimplexOfMap_face]
  change singularSimplexChain X (singularSimplexOfMap X
      ((pathHomotopyUpperTriangle F).comp (triangleFaceMap 0))) -
    singularSimplexChain X (singularSimplexOfMap X
      ((pathHomotopyUpperTriangle F).comp (triangleFaceMap 1))) +
    singularSimplexChain X (singularSimplexOfMap X
      ((pathHomotopyUpperTriangle F).comp (triangleFaceMap 2))) = _
  rw [pathHomotopyUpperTriangle_face_zero, pathHomotopyUpperTriangle_face_one,
    pathHomotopyUpperTriangle_face_two]
  rfl

theorem singularHomotopyChain_difference_boundary (F : Path.Homotopy γ δ) :
    (integralSingularChainComplex X).d 2 1
      (singularHomotopyLowerChain X F - singularHomotopyUpperChain X F) =
      singularPathChain X δ - singularPathChain X γ +
        singularPathChain X (Path.refl a) - singularPathChain X (Path.refl b) := by
  rw [map_sub, singularHomotopyLowerChain_boundary, singularHomotopyUpperChain_boundary]
  abel

/-- The actual constant two-simplex chain, in the unnormalized singular complex. -/
def singularConstantTwoChain (x : X) : (integralSingularChainComplex X).X 2 :=
  singularSimplexChain X (singularSimplexOfMap X (ContinuousMap.const _ x))

/-- A constant one-simplex need not be the zero chain: it is an actual boundary. -/
theorem singularConstantTwoChain_boundary (x : X) :
    (integralSingularChainComplex X).d 2 1 (singularConstantTwoChain X x) =
      singularPathChain X (Path.refl x) := by
  rw [singularConstantTwoChain, singularSimplexChain_boundary_two]
  simp only [singularSimplexOfMap_face]
  change singularPathChain X (Path.refl x) - singularPathChain X (Path.refl x) +
    singularPathChain X (Path.refl x) = _
  abel

/-- Correcting the two homotopy triangles by actual constant boundaries
produces the literal difference of the two oriented path chains. -/
def singularHomotopyDifferenceChain (F : Path.Homotopy γ δ) :
    (integralSingularChainComplex X).X 2 :=
  singularHomotopyLowerChain X F - singularHomotopyUpperChain X F -
    singularConstantTwoChain X a + singularConstantTwoChain X b

theorem singularHomotopyDifferenceChain_boundary (F : Path.Homotopy γ δ) :
    (integralSingularChainComplex X).d 2 1 (singularHomotopyDifferenceChain X F) =
      singularPathChain X δ - singularPathChain X γ := by
  rw [singularHomotopyDifferenceChain, map_add, map_sub,
    singularHomotopyChain_difference_boundary, singularConstantTwoChain_boundary,
    singularConstantTwoChain_boundary]
  abel

/-- Relative homotopic based loops have the same class in the actual
integral singular H1 object, proved by the displayed genuine two-boundary. -/
theorem singularLoopClass_homotopy {x : X} {γ0 γ1 : Path x x}
    (F : Path.Homotopy γ0 γ1) : singularLoopClass X γ0 = singularLoopClass X γ1 := by
  let K := integralSingularChainComplex X
  let c := singularHomotopyDifferenceChain X F
  have hc : singularLoopCycle X γ1 - singularLoopCycle X γ0 = K.toCycles 2 1 c := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles 1)).mp inferInstance
    rw [map_sub, singularLoopCycle_iCycles, singularLoopCycle_iCycles]
    change _ = (K.toCycles 2 1 ≫ K.iCycles 1) c
    rw [K.toCycles_i]
    exact (singularHomotopyDifferenceChain_boundary X F).symm
  symm
  apply sub_eq_zero.mp
  change K.homologyπ 1 (singularLoopCycle X γ1) - K.homologyπ 1 (singularLoopCycle X γ0) = 0
  rw [← map_sub, hc]
  change (K.toCycles 2 1 ≫ K.homologyπ 1) c = 0
  rw [K.toCycles_comp_homologyπ]
  rfl

/-- The constant loop has zero class in actual integral singular H1,
because its actual one-simplex is the displayed two-boundary. -/
@[simp] theorem singularLoopClass_refl (x : X) : singularLoopClass X (Path.refl x) = 0 := by
  let K := integralSingularChainComplex X
  let c := singularConstantTwoChain X x
  have hc : singularLoopCycle X (Path.refl x) = K.toCycles 2 1 c := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles 1)).mp inferInstance
    rw [singularLoopCycle_iCycles]
    change _ = (K.toCycles 2 1 ≫ K.iCycles 1) c
    rw [K.toCycles_i]
    exact (singularConstantTwoChain_boundary X x).symm
  change K.homologyπ 1 (singularLoopCycle X (Path.refl x)) = 0
  rw [hc]
  change (K.toCycles 2 1 ≫ K.homologyπ 1) c = 0
  rw [K.toCycles_comp_homologyπ]
  rfl

/-- Actual loop concatenation is addition of the corresponding actual
integral singular H1 classes. -/
theorem singularLoopClass_trans {x : X} (γ0 γ1 : Path x x) :
    singularLoopClass X (γ0.trans γ1) = singularLoopClass X γ0 + singularLoopClass X γ1 := by
  let K := integralSingularChainComplex X
  let c := singularConcatTriangleChain X γ0 γ1
  have hc : singularLoopCycle X γ1 - singularLoopCycle X (γ0.trans γ1) +
      singularLoopCycle X γ0 = K.toCycles 2 1 c := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles 1)).mp inferInstance
    rw [map_add, map_sub, singularLoopCycle_iCycles, singularLoopCycle_iCycles,
      singularLoopCycle_iCycles]
    change _ = (K.toCycles 2 1 ≫ K.iCycles 1) c
    rw [K.toCycles_i]
    exact (singularConcatTriangleChain_boundary X γ0 γ1).symm
  have hz : singularLoopClass X γ1 - singularLoopClass X (γ0.trans γ1) +
      singularLoopClass X γ0 = 0 := by
    change K.homologyπ 1 (singularLoopCycle X γ1) -
      K.homologyπ 1 (singularLoopCycle X (γ0.trans γ1)) +
      K.homologyπ 1 (singularLoopCycle X γ0) = 0
    rw [← map_sub, ← map_add, hc]
    change (K.toCycles 2 1 ≫ K.homologyπ 1) c = 0
    rw [K.toCycles_comp_homologyπ]
    rfl
  have he : (singularLoopClass X γ0 + singularLoopClass X γ1) -
      singularLoopClass X (γ0.trans γ1) = 0 := by
    calc
      _ = singularLoopClass X γ1 - singularLoopClass X (γ0.trans γ1) +
          singularLoopClass X γ0 := by abel
      _ = 0 := hz
  exact (sub_eq_zero.mp he).symm

end Markov
