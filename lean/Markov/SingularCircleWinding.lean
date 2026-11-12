import Markov.NormalizedCircleWinding
import Markov.SingularHurewiczInverse

/-! Actual integral singular-H1 winding detectors. The construction uses the
proved actual Hurewicz equivalence and algebraic abelianization universality;
no assumed functor naturality or comparison field is used. -/

noncomputable section
namespace Markov

/-- Actual fundamental-group winding induced by a continuous circle-valued map,
with its basepoint value identified with the zero class. -/
def fundamentalGroupCircleWinding {X : Type} [TopologicalSpace X]
    (x : X) (r : X → NormalizedCircle) (hr : Continuous r) (hrx : r x = 0) :
    FundamentalGroup X x →* Multiplicative ℤ :=
  normalizedCircleFundamentalGroupEquiv.toMonoidHom.comp
    (FundamentalGroup.mapOfEq ⟨r, hr⟩ hrx)

/-- The actual singular-H1 detector induced by a circle-valued map, using
specified actual connecting paths and the proved genuine Hurewicz inverse. -/
def singularH1CircleWinding {X : Type} [TopologicalSpace X]
    (x : X) (τ : ∀ y : X, Path x y)
    (r : X → NormalizedCircle) (hr : Continuous r) (hrx : r x = 0) :
    integralSingularH1 X →+ ℤ :=
  (Abelianization.lift (fundamentalGroupCircleWinding x r hr hrx)).toAdditiveLeft.comp
    (singularHurewiczAddEquiv X x τ).symm.toAddMonoidHom

/-- Exact evaluation on the literal oriented singular class of any actual loop. -/
theorem singularH1CircleWinding_loop {X : Type} [TopologicalSpace X]
    (x : X) (τ : ∀ y : X, Path x y)
    (r : X → NormalizedCircle) (hr : Continuous r) (hrx : r x = 0)
    (γ : Path x x) :
    singularH1CircleWinding x τ r hr hrx (singularLoopClass X γ) =
      normalizedCircleWinding ((γ.map hr).cast hrx.symm hrx.symm) := by
  change (Abelianization.lift (fundamentalGroupCircleWinding x r hr hrx)).toAdditiveLeft
    ((singularHurewiczAddEquiv X x τ).symm (singularLoopClass X γ)) = _
  rw [← singularHurewiczAddEquiv_loop X x τ γ, AddEquiv.symm_apply_apply]
  change Multiplicative.toAdd (fundamentalGroupCircleWinding x r hr hrx
    (FundamentalGroup.fromPath (.mk γ))) = _
  unfold fundamentalGroupCircleWinding
  rw [MonoidHom.comp_apply, FundamentalGroup.mapOfEq_apply]
  rfl

/-- Mapping the positive standard loop into a continuous circle retract gives
an actual singular-H1 class on which an actual integer-valued homomorphism is 1. -/
theorem singularH1CircleWinding_retract_standardLoop
    {X : Type} [TopologicalSpace X]
    {f : NormalizedCircle → X} {r : X → NormalizedCircle}
    (hf : Continuous f) (hr : Continuous r) (hleft : Function.LeftInverse r f)
    (τ : ∀ y : X, Path (f 0) y) :
    singularH1CircleWinding (f 0) τ r hr (hleft 0)
      (singularLoopClass X (normalizedCircleStandardLoop.map hf)) = 1 := by
  rw [singularH1CircleWinding_loop]
  have hγ : (((normalizedCircleStandardLoop.map hf).map hr).cast
      (hleft 0).symm (hleft 0).symm) = normalizedCircleStandardLoop := by
    ext t
    exact hleft (normalizedCircleStandardLoop t)
  rw [hγ, normalizedCircleWinding_standardLoop]

/-- The positive loop on every continuous circle retract has a nonzero class
in the genuine integral singular homology object. -/
theorem singularLoopClass_retract_standardLoop_ne_zero
    {X : Type} [TopologicalSpace X]
    {f : NormalizedCircle → X} {r : X → NormalizedCircle}
    (hf : Continuous f) (hr : Continuous r) (hleft : Function.LeftInverse r f)
    (τ : ∀ y : X, Path (f 0) y) :
    singularLoopClass X (normalizedCircleStandardLoop.map hf) ≠ 0 := by
  intro hz
  have hw := singularH1CircleWinding_retract_standardLoop hf hr hleft τ
  rw [hz, map_zero] at hw
  exact zero_ne_one hw

end Markov
