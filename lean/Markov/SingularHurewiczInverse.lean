import Markov.SingularChainAbelianization
import Markov.SingularBasedLoopBoundary

/-! Explicit actual chain identities for the reverse Hurewicz inverse law.
All maps use the pinned integral singular chain complex and explicit connecting
paths. No homology-generation statement or Hurewicz equivalence is assumed. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
namespace Markov

private def inverseIntegerCoefficient {B : AddCommGrpCat.{0}} (b : B) : AddCommGrpCat.of ℤ ⟶ B :=
  AddCommGrpCat.ofHom
    { toFun := fun n => n • b
      map_zero' := zero_zsmul _
      map_add' := fun _ _ => add_zsmul _ _ _ }

private theorem inverseSigmaDesc_eval {I : Type} {B : AddCommGrpCat.{0}} (f : I → B) (i : I) :
    Sigma.desc (fun j => inverseIntegerCoefficient (f j))
      ((Sigma.ι (fun _ : I => AddCommGrpCat.of ℤ) i) (1 : ℤ)) = f i := by
  have hh := Sigma.ι_desc (fun j => inverseIntegerCoefficient (f j)) i
  have he := congrArg (fun g : AddCommGrpCat.of ℤ ⟶ B => g (1 : ℤ)) hh
  change _ = (1 : ℤ) • f i at he
  simpa only [one_zsmul] using he

private theorem inverseIntegerHom_ext {B : AddCommGrpCat.{0}}
    (f g : AddCommGrpCat.of ℤ ⟶ B) (h : f (1 : ℤ) = g (1 : ℤ)) : f = g := by
  apply AddCommGrpCat.ext
  intro n
  change f n = g n
  have hf : f n = n • f (1 : ℤ) := by
    simpa only [zsmul_eq_mul, mul_one] using map_zsmul f.hom n (1 : ℤ)
  have hg : g n = n • g (1 : ℤ) := by
    simpa only [zsmul_eq_mul, mul_one] using map_zsmul g.hom n (1 : ℤ)
  rw [hf, hg, h]

variable (X : Type) [TopologicalSpace X] (x : X) (τ : ∀ y : X, Path x y)

/-- The literal actual based loop closing an actual singular edge. -/
def singularConnectedLoop (σ : IntegralSingularSimplex X 1) : Path x x :=
  ((τ (singularSimplexVertex X σ 0)).trans (singularEdgePath X σ)).trans
    (τ (singularSimplexVertex X σ 1)).symm

/-- Actual cycle-valued closure of the actual one-chain coproduct generators. -/
def singularLoopCycleClosure :
    (integralSingularChainComplex X).X 1 ⟶ (integralSingularChainComplex X).cycles 1 :=
  Sigma.desc (fun σ : IntegralSingularSimplex X 1 =>
    inverseIntegerCoefficient (singularLoopCycle X (singularConnectedLoop X x τ σ)))

theorem singularLoopCycleClosure_simplex (σ : IntegralSingularSimplex X 1) :
    singularLoopCycleClosure X x τ (singularSimplexChain X σ) =
      singularLoopCycle X (singularConnectedLoop X x τ σ) :=
  inverseSigmaDesc_eval _ σ

/-- The actual connecting one-chain attached to each actual zero-simplex. -/
def singularConnectorZeroChain :
    (integralSingularChainComplex X).X 0 ⟶ (integralSingularChainComplex X).X 1 :=
  Sigma.desc (fun σ : IntegralSingularSimplex X 0 =>
    inverseIntegerCoefficient (singularPathChain X (τ (singularSimplexVertex X σ 0))))

theorem singularConnectorZeroChain_simplex (σ : IntegralSingularSimplex X 0) :
    singularConnectorZeroChain X x τ (singularSimplexChain X σ) =
      singularPathChain X (τ (singularSimplexVertex X σ 0)) :=
  inverseSigmaDesc_eval _ σ

theorem singularConnectorZeroChain_point (y : X) :
    singularConnectorZeroChain X x τ (singularPointChain X y) = singularPathChain X (τ y) := by
  rw [singularPointChain, singularConnectorZeroChain_simplex]
  have he : singularSimplexVertex X (singularPointSimplex X y) 0 = y := by
    unfold singularSimplexVertex singularPointSimplex
    rw [singularSimplexMap_ofMap]
    rfl
  rw [he]

/-- An actual two-chain morphism providing the explicit connecting-path correction. -/
def singularLoopClosureTwoChain :
    (integralSingularChainComplex X).X 1 ⟶ (integralSingularChainComplex X).X 2 :=
  Sigma.desc (fun σ : IntegralSingularSimplex X 1 =>
    inverseIntegerCoefficient (singularBasedLoopTwoChain X
      (τ (singularSimplexVertex X σ 0)) (singularEdgePath X σ)
      (τ (singularSimplexVertex X σ 1))))

theorem singularLoopClosureTwoChain_simplex (σ : IntegralSingularSimplex X 1) :
    singularLoopClosureTwoChain X x τ (singularSimplexChain X σ) =
      singularBasedLoopTwoChain X (τ (singularSimplexVertex X σ 0)) (singularEdgePath X σ)
        (τ (singularSimplexVertex X σ 1)) :=
  inverseSigmaDesc_eval _ σ

/-- The literal chain identity on every actual singular generator. -/
theorem singularLoopClosure_chain_identity_simplex (σ : IntegralSingularSimplex X 1) :
    (integralSingularChainComplex X).iCycles 1
      (singularLoopCycleClosure X x τ (singularSimplexChain X σ)) - singularSimplexChain X σ +
        singularConnectorZeroChain X x τ
          ((integralSingularChainComplex X).d 1 0 (singularSimplexChain X σ)) =
      (integralSingularChainComplex X).d 2 1
        (singularLoopClosureTwoChain X x τ (singularSimplexChain X σ)) := by
  rw [singularLoopCycleClosure_simplex, singularLoopCycle_iCycles,
    singularLoopClosureTwoChain_simplex, singularSimplexChain_boundary_edge,
    map_sub, singularConnectorZeroChain_point, singularConnectorZeroChain_point,
    singularBasedLoopTwoChain_boundary, singularPathChain_edgePath]
  change singularPathChain X (singularConnectedLoop X x τ σ) - singularSimplexChain X σ +
    (singularPathChain X (τ (singularSimplexVertex X σ 1)) -
      singularPathChain X (τ (singularSimplexVertex X σ 0))) =
    singularPathChain X (singularConnectedLoop X x τ σ) - singularSimplexChain X σ -
      singularPathChain X (τ (singularSimplexVertex X σ 0)) +
      singularPathChain X (τ (singularSimplexVertex X σ 1))
  abel

/-- The actual full chain morphism identity, proved by coproduct universality
and all integer coefficients, rather than an assumed cycle-generation theorem. -/
theorem singularLoopClosure_chain_identity :
    singularLoopCycleClosure X x τ ≫ (integralSingularChainComplex X).iCycles 1 -
      𝟙 ((integralSingularChainComplex X).X 1) +
      (integralSingularChainComplex X).d 1 0 ≫ singularConnectorZeroChain X x τ =
        singularLoopClosureTwoChain X x τ ≫ (integralSingularChainComplex X).d 2 1 := by
  apply Sigma.hom_ext
  intro σ
  apply inverseIntegerHom_ext
  change (integralSingularChainComplex X).iCycles 1
    (singularLoopCycleClosure X x τ (singularSimplexChain X σ)) - singularSimplexChain X σ +
      singularConnectorZeroChain X x τ
        ((integralSingularChainComplex X).d 1 0 (singularSimplexChain X σ)) =
    (integralSingularChainComplex X).d 2 1
      (singularLoopClosureTwoChain X x τ (singularSimplexChain X σ))
  exact singularLoopClosure_chain_identity_simplex X x τ σ

/-- The actual additive Hurewicz homomorphism, as a morphism of abelian groups. -/
def singularHurewiczAddHom :
    AddCommGrpCat.of (BasedLoopAbelianGroup X x) ⟶ integralSingularH1 X :=
  AddCommGrpCat.ofHom (singularHurewiczAbelianizationAdd X x)

/-- On every actual chain, taking the based class then Hurewicz agrees
with actual cycle closure followed by the actual homology projection. -/
theorem singularOneChainToAbelianization_hurewicz :
    singularOneChainToAbelianization X x τ ≫ singularHurewiczAddHom X x =
      singularLoopCycleClosure X x τ ≫ (integralSingularChainComplex X).homologyπ 1 := by
  apply Sigma.hom_ext
  intro σ
  apply inverseIntegerHom_ext
  change singularHurewiczAddHom X x
    (singularOneChainToAbelianization X x τ (singularSimplexChain X σ)) =
      (integralSingularChainComplex X).homologyπ 1
        (singularLoopCycleClosure X x τ (singularSimplexChain X σ))
  rw [singularOneChainToAbelianization_simplex, singularLoopCycleClosure_simplex]
  change singularHurewiczAbelianizationAdd X x
    (Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      (.mk (singularConnectedLoop X x τ σ))))) =
    singularLoopClass X (singularConnectedLoop X x τ σ)
  exact singularHurewiczAbelianizationAdd_loop X _

/-- Restricting the literal chain identity to actual cycles makes the
connecting correction vanish and the remaining difference a genuine boundary. -/
theorem singularLoopClosure_cycle_difference (c : (integralSingularChainComplex X).cycles 1) :
    singularLoopCycleClosure X x τ ((integralSingularChainComplex X).iCycles 1 c) - c =
      (integralSingularChainComplex X).toCycles 2 1
        (singularLoopClosureTwoChain X x τ ((integralSingularChainComplex X).iCycles 1 c)) := by
  let K := integralSingularChainComplex X
  apply (AddCommGrpCat.mono_iff_injective (K.iCycles 1)).mp inferInstance
  rw [map_sub]
  change _ = (K.toCycles 2 1 ≫ K.iCycles 1)
    (singularLoopClosureTwoChain X x τ (K.iCycles 1 c))
  rw [K.toCycles_i]
  have he := congrArg (fun f : K.X 1 ⟶ K.X 1 => f (K.iCycles 1 c))
    (singularLoopClosure_chain_identity X x τ)
  change K.iCycles 1 (singularLoopCycleClosure X x τ (K.iCycles 1 c)) - K.iCycles 1 c +
    singularConnectorZeroChain X x τ (K.d 1 0 (K.iCycles 1 c)) =
      K.d 2 1 (singularLoopClosureTwoChain X x τ (K.iCycles 1 c)) at he
  have hz := congrArg (fun f : K.cycles 1 ⟶ K.X 0 => f c) (K.iCycles_d 1 0)
  change K.d 1 0 (K.iCycles 1 c) = 0 at hz
  rw [hz, map_zero, add_zero] at he
  exact he

/-- The reverse inverse law first holds after the actual homology projection. -/
theorem singularHurewicz_reverse_projection :
    (integralSingularChainComplex X).homologyπ 1 ≫ singularHomologyToAbelianization X x τ ≫
      singularHurewiczAddHom X x = (integralSingularChainComplex X).homologyπ 1 := by
  rw [← Category.assoc, singularHomologyToAbelianization_projection,
    Category.assoc, singularOneChainToAbelianization_hurewicz]
  apply AddCommGrpCat.ext
  intro c
  change (integralSingularChainComplex X).homologyπ 1
    (singularLoopCycleClosure X x τ ((integralSingularChainComplex X).iCycles 1 c)) =
      (integralSingularChainComplex X).homologyπ 1 c
  apply sub_eq_zero.mp
  rw [← map_sub, singularLoopClosure_cycle_difference]
  change ((integralSingularChainComplex X).toCycles 2 1 ≫
    (integralSingularChainComplex X).homologyπ 1)
      (singularLoopClosureTwoChain X x τ ((integralSingularChainComplex X).iCycles 1 c)) = 0
  rw [HomologicalComplex.toCycles_comp_homologyπ]
  rfl

/-- Cancellation of the genuine epi homology projection yields the actual
reverse inverse law on all singular H1, without assuming generators. -/
theorem singularHurewicz_reverse_morphism :
    singularHomologyToAbelianization X x τ ≫ singularHurewiczAddHom X x =
      𝟙 (integralSingularH1 X) := by
  apply (cancel_epi ((integralSingularChainComplex X).homologyπ 1)).mp
  rw [singularHurewicz_reverse_projection]
  change (integralSingularChainComplex X).homologyπ 1 =
    (integralSingularChainComplex X).homologyπ 1 ≫
      𝟙 ((integralSingularChainComplex X).homology 1)
  exact (Category.comp_id _).symm

theorem singularHomologyToAbelianization_rightInverse :
    Function.RightInverse (singularHomologyToAbelianization X x τ)
      (singularHurewiczAbelianizationAdd X x) := by
  intro c
  exact congrArg (fun f : integralSingularH1 X ⟶ integralSingularH1 X => f c)
    (singularHurewicz_reverse_morphism X x τ)

/-- The genuine normalized degree-one Hurewicz additive equivalence,
proved through both actual inverse laws for the given actual connecting paths. -/
def singularHurewiczAddEquiv :
    BasedLoopAbelianGroup X x ≃+ integralSingularH1 X where
  toFun := singularHurewiczAbelianizationAdd X x
  invFun := singularHomologyToAbelianization X x τ
  left_inv := singularHomologyToAbelianization_leftInverse X x τ
  right_inv := singularHomologyToAbelianization_rightInverse X x τ
  map_add' := map_add _

@[simp] theorem singularHurewiczAddEquiv_loop (γ : Path x x) :
    singularHurewiczAddEquiv X x τ
      (Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath (.mk γ)))) =
        singularLoopClass X γ :=
  singularHurewiczAbelianizationAdd_loop X γ

end Markov
