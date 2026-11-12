import Markov.BasedHomeomorphFundamentalGroup

noncomputable section
namespace Markov

/-- The actual connector for f after g: first travel to f(x), then traverse
the actual f-image of the connector from x to g(x). -/
def basedHomeomorphCompositeConnector {X : Type*} [TopologicalSpace X]
    (f g : X ≃ₜ X) (x : X) (cf : Path x (f x)) (cg : Path x (g x)) :
    Path x ((g.trans f) x) :=
  cf.trans (cg.map f.continuous)

/-- Composition of actual homeomorphism-and-connector pi1 realizations.
Homeomorph.trans and MulEquiv.trans orders are both retained explicitly. -/
theorem basedHomeomorphFundamentalGroupEquiv_comp {X : Type*} [TopologicalSpace X]
    (f g : X ≃ₜ X) (x : X) (cf : Path x (f x)) (cg : Path x (g x)) :
    (basedHomeomorphFundamentalGroupEquiv g x cg).trans
      (basedHomeomorphFundamentalGroupEquiv f x cf) =
    basedHomeomorphFundamentalGroupEquiv (g.trans f) x
      (basedHomeomorphCompositeConnector f g x cf cg) := by
  apply MulEquiv.ext
  intro a
  induction a using Path.Homotopic.Quotient.ind with
  | mk γ =>
    rw [MulEquiv.trans_apply, basedHomeomorphFundamentalGroupEquiv_loop,
      basedHomeomorphFundamentalGroupEquiv_loop, basedHomeomorphFundamentalGroupEquiv_loop]
    change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
    simp only [basedHomeomorphCompositeConnector, Path.map_trans, Path.map_symm,
      Path.trans_symm, Path.map_map, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.trans_assoc]

/-- The actual inverse connector is the reversed original connector mapped
through the actual inverse homeomorphism, with its source cast back to x. -/
def basedHomeomorphInverseConnector {X : Type*} [TopologicalSpace X]
    (f : X ≃ₜ X) (x : X) (cf : Path x (f x)) : Path x (f.symm x) :=
  (cf.symm.map f.symm.continuous).cast (f.symm_apply_apply x).symm rfl

/-- Inverting a genuine based realization is the genuine inverse-homeomorphism
realization with the explicit mapped reversed connector. -/
theorem basedHomeomorphFundamentalGroupEquiv_inverse {X : Type*} [TopologicalSpace X]
    (f : X ≃ₜ X) (x : X) (cf : Path x (f x)) :
    basedHomeomorphFundamentalGroupEquiv f.symm x (basedHomeomorphInverseConnector f x cf) =
      (basedHomeomorphFundamentalGroupEquiv f x cf).symm := by
  apply MulEquiv.ext
  intro a
  induction a using Path.Homotopic.Quotient.ind with
  | mk γ =>
    rw [basedHomeomorphFundamentalGroupEquiv_loop, basedHomeomorphFundamentalGroupEquiv_symm_loop]
    apply congrArg FundamentalGroup.fromPath
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    simp only [basedHomeomorphInverseConnector, Path.cast_coe, Path.map_coe,
      Function.comp_apply, Path.trans_apply, Path.symm_apply, unitInterval.symm_symm]
    split_ifs <;> rfl

/-- The actual identity homeomorphism with constant connector gives the
literal identity multiplicative equivalence of the actual fundamental group. -/
theorem basedHomeomorphFundamentalGroupEquiv_refl {X : Type*} [TopologicalSpace X] (x : X) :
    basedHomeomorphFundamentalGroupEquiv (Homeomorph.refl X) x (Path.refl x) =
      MulEquiv.refl (FundamentalGroup X x) := by
  apply MulEquiv.ext
  intro a
  induction a using Path.Homotopic.Quotient.ind with
  | mk γ =>
    rw [basedHomeomorphFundamentalGroupEquiv_loop]
    change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk γ
    have hm : γ.map (Homeomorph.refl X).continuous = γ := by ext t; rfl
    rw [hm, Path.refl_symm, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_refl,
      Path.Homotopic.Quotient.refl_trans]
    exact Path.Homotopic.Quotient.trans_refl (.mk γ)

end Markov
