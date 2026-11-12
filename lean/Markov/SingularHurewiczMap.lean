import Markov.SingularHomotopyBoundary
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Group.TypeTags.Hom

/-! The normalized degree-one Hurewicz homomorphism into the actual integral
singular homology object. Positive oriented loops map to their actual singular
one-cycle classes. Reversed End multiplication is handled by commutativity of
H1, without reversing the loop. No Hurewicz equivalence, injectivity,
surjectivity or identification of H1 with algebraic abelianization is claimed. -/

noncomputable section
namespace Markov

variable (X : Type) [TopologicalSpace X]

/-- The actual singular H1 class of a loop homotopy class. -/
def singularLoopClassQuotient (x : X) :
    Path.Homotopic.Quotient x x → integralSingularH1 X :=
  _root_.Quotient.lift (fun γ : Path x x => singularLoopClass X γ)
    (fun _ _ h => h.elim (fun F => singularLoopClass_homotopy X F))

@[simp] theorem singularLoopClassQuotient_mk {x : X} (γ : Path x x) :
    singularLoopClassQuotient X x (.mk γ) = singularLoopClass X γ := rfl

@[simp] theorem singularLoopClassQuotient_refl (x : X) :
    singularLoopClassQuotient X x (.refl x) = 0 :=
  singularLoopClass_refl X x

theorem singularLoopClassQuotient_trans {x : X}
    (c d : Path.Homotopic.Quotient x x) :
    singularLoopClassQuotient X x (c.trans d) =
      singularLoopClassQuotient X x c + singularLoopClassQuotient X x d := by
  refine Path.Homotopic.Quotient.ind₂ (fun γ δ => ?_) c d
  exact singularLoopClass_trans X γ δ

/-- The normalized actual pi1-to-singular-H1 group homomorphism.
The target is the multiplicative type tag of the actual additive H1 group. -/
def singularHurewiczMap (x : X) :
    FundamentalGroup X x →* Multiplicative (integralSingularH1 X) where
  toFun c := Multiplicative.ofAdd (singularLoopClassQuotient X x c.toPath)
  map_one' := by
    change Multiplicative.ofAdd (singularLoopClassQuotient X x (.refl x)) = 1
    rw [singularLoopClassQuotient_refl]
    rfl
  map_mul' c d := by
    change Multiplicative.ofAdd (singularLoopClassQuotient X x (d.toPath.trans c.toPath)) = _
    rw [singularLoopClassQuotient_trans]
    change Multiplicative.ofAdd (singularLoopClassQuotient X x d.toPath +
      singularLoopClassQuotient X x c.toPath) =
      Multiplicative.ofAdd (singularLoopClassQuotient X x c.toPath +
        singularLoopClassQuotient X x d.toPath)
    exact congrArg Multiplicative.ofAdd (add_comm _ _)

/-- Exact positive-loop normalization, with no inversion or sign change. -/
@[simp] theorem singularHurewiczMap_loop {x : X} (γ : Path x x) :
    singularHurewiczMap X x (FundamentalGroup.fromPath (.mk γ)) =
      Multiplicative.ofAdd (singularLoopClass X γ) := rfl

/-- The universal descent of the actual Hurewicz map through actual
algebraic abelianization. This remains a homomorphism, not an equivalence. -/
def singularHurewiczAbelianization (x : X) :
    Abelianization (FundamentalGroup X x) →* Multiplicative (integralSingularH1 X) :=
  Abelianization.lift (singularHurewiczMap X x)

@[simp] theorem singularHurewiczAbelianization_of {x : X}
    (c : FundamentalGroup X x) :
    singularHurewiczAbelianization X x (Abelianization.of c) = singularHurewiczMap X x c := rfl

@[simp] theorem singularHurewiczAbelianization_loop {x : X} (γ : Path x x) :
    singularHurewiczAbelianization X x
      (Abelianization.of (FundamentalGroup.fromPath (.mk γ))) =
        Multiplicative.ofAdd (singularLoopClass X γ) := rfl

/-- The same descent in additive notation, with the actual additive H1 target. -/
def singularHurewiczAbelianizationAdd (x : X) :
    Additive (Abelianization (FundamentalGroup X x)) →+ integralSingularH1 X :=
  (singularHurewiczAbelianization X x).toAdditiveLeft

@[simp] theorem singularHurewiczAbelianizationAdd_loop {x : X} (γ : Path x x) :
    singularHurewiczAbelianizationAdd X x
      (Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath (.mk γ)))) =
        singularLoopClass X γ := rfl

end Markov
