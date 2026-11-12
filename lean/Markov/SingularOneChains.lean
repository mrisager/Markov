import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Tactic
import Markov.PathTriangle

/-! Actual integral singular chains, oriented path boundaries and loop classes.
The chain complex and degree-one homology object are the pinned mathlib
singular functors with coefficient group Z. No replacement quotient or
Hurewicz assumption is introduced. All small topological spaces are covered,
including the actual modular orbit quotient. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
open Simplicial
namespace Markov

private def singularIdentityForget : HasForget₂ AddCommGrpCat.{0} AddCommGrpCat.{0} where
  forget₂ := 𝟭 _
  forget_comp := rfl

attribute [local instance] singularIdentityForget

private def singularIdentityForgetAdditive : (forget₂ AddCommGrpCat.{0} AddCommGrpCat.{0}).Additive := by
  change (𝟭 AddCommGrpCat.{0}).Additive
  infer_instance

attribute [local instance] singularIdentityForgetAdditive

private def singularIdentityForgetHomology :
    (forget₂ AddCommGrpCat.{0} AddCommGrpCat.{0}).PreservesHomology := by
  change (𝟭 AddCommGrpCat.{0}).PreservesHomology
  infer_instance

attribute [local instance] singularIdentityForgetHomology

variable (X : Type) [TopologicalSpace X]

/-- The actual pinned integral singular chain complex. -/
def integralSingularChainComplex : ChainComplex AddCommGrpCat ℕ :=
  ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)

/-- The actual pinned integral singular homology object in degree one. -/
def integralSingularH1 : AddCommGrpCat :=
  ((singularHomologyFunctor AddCommGrpCat 1).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)

abbrev IntegralSingularSimplex (n : ℕ) : Type :=
  (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)

/-- The categorical coproduct generator evaluated at the integer 1. -/
def singularSimplexChain {n : ℕ} (σ : IntegralSingularSimplex X n) :
    (integralSingularChainComplex X).X n :=
  (Sigma.ι (fun _ : IntegralSingularSimplex X n => AddCommGrpCat.of ℤ) σ) (1 : ℤ)

/-- Continuous simplex maps give actual singular-set simplices. -/
def singularSimplexOfMap {n : ℕ} (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    IntegralSingularSimplex X n :=
  (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm σ

/-- Continuous simplex face restriction agrees with the actual singular-set face. -/
theorem singularSimplexOfMap_face {n : ℕ} (i : Fin (n + 2))
    (σ : C(stdSimplex ℝ (Fin (n + 2)), X)) :
    (TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.δ i).op
      (singularSimplexOfMap X σ) =
        singularSimplexOfMap X (σ.comp
          ⟨stdSimplex.map (SimplexCategory.δ i), stdSimplex.continuous_map _⟩) := by
  rfl

/-- The actual constant singular zero-simplex at a point. -/
def singularPointSimplex (x : X) : IntegralSingularSimplex X 0 :=
  singularSimplexOfMap X (ContinuousMap.const _ x)

/-- The actual oriented singular one-simplex of a path. -/
def singularPathSimplex {a b : X} (γ : Path a b) : IntegralSingularSimplex X 1 :=
  singularSimplexOfMap X (γ.toContinuousMap.comp ⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩)

def singularPointChain (x : X) : (integralSingularChainComplex X).X 0 :=
  singularSimplexChain X (singularPointSimplex X x)

def singularPathChain {a b : X} (γ : Path a b) : (integralSingularChainComplex X).X 1 :=
  singularSimplexChain X (singularPathSimplex X γ)

/-- The actual face homomorphism on the coproduct chain group. -/
def singularFaceHom (n : ℕ) (i : Fin (n + 2)) :
    (integralSingularChainComplex X).X (n + 1) ⟶ (integralSingularChainComplex X).X n :=
  Sigma.map' ((TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.δ i).op)
    (fun _ => 𝟙 (AddCommGrpCat.of ℤ))

theorem integralSingularChainComplex_d_eq (n : ℕ) :
    (integralSingularChainComplex X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • singularFaceHom X n i := by
  change (AlternatingFaceMapComplex.obj ((TopCat.toSSet.obj (TopCat.of X)) ⋙
    (sigmaConst.obj (AddCommGrpCat.of ℤ)))).d (n + 1) n = _
  rw [AlternatingFaceMapComplex.obj_d_eq]
  rfl

theorem singularFaceHom_simplexChain {n : ℕ} (i : Fin (n + 2))
    (σ : IntegralSingularSimplex X (n + 1)) :
    singularFaceHom X n i (singularSimplexChain X σ) =
      singularSimplexChain X
        ((TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.δ i).op σ) := by
  have hh := Sigma.ι_comp_map'
    (f := fun _ : IntegralSingularSimplex X (n + 1) => AddCommGrpCat.of ℤ)
    (g := fun _ : IntegralSingularSimplex X n => AddCommGrpCat.of ℤ)
    ((TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.δ i).op)
    (fun _ => 𝟙 (AddCommGrpCat.of ℤ)) σ
  exact congrArg (fun f : AddCommGrpCat.of ℤ ⟶ (integralSingularChainComplex X).X n => f (1 : ℤ)) hh

theorem singularPathSimplex_face_zero {a b : X} (γ : Path a b) :
    (TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.δ (0 : Fin 2)).op
      (singularPathSimplex X γ) = singularPointSimplex X b := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋0⦌)).injective
  ext t
  change γ (stdSimplexHomeomorphUnitInterval
    (stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) t)) = b
  have ht : t = stdSimplex.vertex (S := ℝ) (0 : Fin 1) :=
    @Subsingleton.elim (stdSimplex ℝ (Fin 1)) inferInstance t _
  rw [ht, stdSimplex.map_vertex]
  exact γ.target

theorem singularPathSimplex_face_one {a b : X} (γ : Path a b) :
    (TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.δ (1 : Fin 2)).op
      (singularPathSimplex X γ) = singularPointSimplex X a := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋0⦌)).injective
  ext t
  change γ (stdSimplexHomeomorphUnitInterval
    (stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) t)) = a
  have ht : t = stdSimplex.vertex (S := ℝ) (0 : Fin 1) :=
    @Subsingleton.elim (stdSimplex ℝ (Fin 1)) inferInstance t _
  rw [ht, stdSimplex.map_vertex]
  exact γ.source

theorem singularSimplexChain_boundary_one (σ : IntegralSingularSimplex X 1) :
    (integralSingularChainComplex X).d 1 0 (singularSimplexChain X σ) =
      singularSimplexChain X ((TopCat.toSSet.obj (TopCat.of X)).map
        (SimplexCategory.δ (0 : Fin 2)).op σ) -
      singularSimplexChain X ((TopCat.toSSet.obj (TopCat.of X)).map
        (SimplexCategory.δ (1 : Fin 2)).op σ) := by
  have hd : (integralSingularChainComplex X).d 1 0 =
      singularFaceHom X 0 0 - singularFaceHom X 0 1 := by
    rw [integralSingularChainComplex_d_eq]
    simp [Fin.sum_univ_two, sub_eq_add_neg]
  rw [hd]
  change singularFaceHom X 0 0 (singularSimplexChain X σ) -
    singularFaceHom X 0 1 (singularSimplexChain X σ) = _
  rw [singularFaceHom_simplexChain, singularFaceHom_simplexChain]

theorem singularSimplexChain_boundary_two (σ : IntegralSingularSimplex X 2) :
    (integralSingularChainComplex X).d 2 1 (singularSimplexChain X σ) =
      singularSimplexChain X ((TopCat.toSSet.obj (TopCat.of X)).map
        (SimplexCategory.δ (0 : Fin 3)).op σ) -
      singularSimplexChain X ((TopCat.toSSet.obj (TopCat.of X)).map
        (SimplexCategory.δ (1 : Fin 3)).op σ) +
      singularSimplexChain X ((TopCat.toSSet.obj (TopCat.of X)).map
        (SimplexCategory.δ (2 : Fin 3)).op σ) := by
  have hd : (integralSingularChainComplex X).d 2 1 =
      singularFaceHom X 1 0 - singularFaceHom X 1 1 + singularFaceHom X 1 2 := by
    rw [integralSingularChainComplex_d_eq]
    simp [Fin.sum_univ_three, sub_eq_add_neg]
  rw [hd]
  change singularFaceHom X 1 0 (singularSimplexChain X σ) -
    singularFaceHom X 1 1 (singularSimplexChain X σ) +
    singularFaceHom X 1 2 (singularSimplexChain X σ) = _
  rw [singularFaceHom_simplexChain, singularFaceHom_simplexChain, singularFaceHom_simplexChain]

/-- The actual oriented path boundary is target minus source. -/
theorem singularPathChain_boundary {a b : X} (γ : Path a b) :
    (integralSingularChainComplex X).d 1 0 (singularPathChain X γ) =
      singularPointChain X b - singularPointChain X a := by
  rw [singularPathChain, singularSimplexChain_boundary_one,
    singularPathSimplex_face_zero, singularPathSimplex_face_one]
  rfl

theorem singularLoopChain_boundary (a : X) (γ : Path a a) :
    (integralSingularChainComplex X).d 1 0 (singularPathChain X γ) = 0 := by
  rw [singularPathChain_boundary, sub_self]

/-- An actual cycle in the actual integral singular chain complex. -/
def singularLoopCycle {a : X} (γ : Path a a) : (integralSingularChainComplex X).cycles 1 :=
  (integralSingularChainComplex X).cyclesMk (i := 1) (singularPathChain X γ) 0
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl))
    (singularLoopChain_boundary X a γ)

/-- The actual cycle inclusion recovers the positively oriented path chain. -/
@[simp] theorem singularLoopCycle_iCycles {a : X} (γ : Path a a) :
    (integralSingularChainComplex X).iCycles 1 (singularLoopCycle X γ) = singularPathChain X γ := by
  exact (integralSingularChainComplex X).i_cyclesMk (i := 1) (singularPathChain X γ) 0
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl))
    (singularLoopChain_boundary X a γ)

/-- The actual integral singular H1 class of an oriented based loop.
No homotopy invariance or Hurewicz equivalence is asserted here. -/
def singularLoopClass {a : X} (γ : Path a a) : integralSingularH1 X :=
  (integralSingularChainComplex X).homologyπ 1 (singularLoopCycle X γ)

/-- The actual singular two-chain of the checked continuous concatenation triangle. -/
def singularConcatTriangleChain {a b c : X} (γ : Path a b) (δ : Path b c) :
    (integralSingularChainComplex X).X 2 :=
  singularSimplexChain X (singularSimplexOfMap X (pathConcatTriangleMap γ δ))

/-- The genuine triangle boundary supplies the oriented concatenation relation
inside the actual integral singular chain complex. -/
theorem singularConcatTriangleChain_boundary {a b c : X} (γ : Path a b) (δ : Path b c) :
    (integralSingularChainComplex X).d 2 1 (singularConcatTriangleChain X γ δ) =
      singularPathChain X δ - singularPathChain X (γ.trans δ) + singularPathChain X γ := by
  rw [singularConcatTriangleChain, singularSimplexChain_boundary_two]
  simp only [singularSimplexOfMap_face]
  change singularSimplexChain X (singularSimplexOfMap X
      ((pathConcatTriangleMap γ δ).comp (triangleFaceMap 0))) -
    singularSimplexChain X (singularSimplexOfMap X
      ((pathConcatTriangleMap γ δ).comp (triangleFaceMap 1))) +
    singularSimplexChain X (singularSimplexOfMap X
      ((pathConcatTriangleMap γ δ).comp (triangleFaceMap 2))) = _
  rw [pathConcatTriangleMap_face_zero, pathConcatTriangleMap_face_one,
    pathConcatTriangleMap_face_two]
  rfl

end Markov
