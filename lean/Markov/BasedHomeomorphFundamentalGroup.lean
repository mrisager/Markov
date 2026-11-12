import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-! Actual fundamental-group equivalences induced by homeomorphisms and an
explicit connecting path. The exact based-loop representative is retained,
with the library's reversed End multiplication respected by actual homomorphisms. -/

noncomputable section
namespace Markov

/-- A homeomorphism induces an actual multiplicative equivalence of fundamental
groups. Its inverse is the actual inverse-map homomorphism with its exact basepoint cast. -/
def homeomorphFundamentalGroupEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) (x : X) : FundamentalGroup X x ≃* FundamentalGroup Y (f x) where
  toFun := FundamentalGroup.map ⟨f, f.continuous⟩ x
  invFun := FundamentalGroup.mapOfEq ⟨f.symm, f.symm.continuous⟩ (f.symm_apply_apply x)
  left_inv g := by
    induction g using Path.Homotopic.Quotient.ind with
    | mk γ =>
      change FundamentalGroup.mapOfEq ⟨f.symm, f.symm.continuous⟩ (f.symm_apply_apply x)
        (FundamentalGroup.fromPath (.mk (γ.map f.continuous))) = FundamentalGroup.fromPath (.mk γ)
      rw [FundamentalGroup.mapOfEq_apply]
      congr 1
      apply congrArg Path.Homotopic.Quotient.mk
      apply Path.ext
      funext t
      exact f.symm_apply_apply (γ t)
  right_inv g := by
    induction g using Path.Homotopic.Quotient.ind with
    | mk γ =>
      change FundamentalGroup.map ⟨f, f.continuous⟩ x
        (FundamentalGroup.mapOfEq ⟨f.symm, f.symm.continuous⟩ (f.symm_apply_apply x)
          (FundamentalGroup.fromPath (.mk γ))) = FundamentalGroup.fromPath (.mk γ)
      rw [FundamentalGroup.mapOfEq_apply]
      change FundamentalGroup.fromPath (.mk
        (((γ.map f.symm.continuous).cast (f.symm_apply_apply x).symm
          (f.symm_apply_apply x).symm).map f.continuous)) = FundamentalGroup.fromPath (.mk γ)
      congr 1
      apply congrArg Path.Homotopic.Quotient.mk
      apply Path.ext
      funext t
      exact f.apply_symm_apply (γ t)
  map_mul' := (FundamentalGroup.map ⟨f, f.continuous⟩ x).map_mul

@[simp] theorem homeomorphFundamentalGroupEquiv_loop
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) (x : X) (γ : Path x x) :
    homeomorphFundamentalGroupEquiv f x (FundamentalGroup.fromPath (.mk γ)) =
      FundamentalGroup.fromPath (.mk (γ.map f.continuous)) := rfl

/-- The genuine inverse is induced by the inverse homeomorphism, including
exact endpoint casts back to the original basepoint. -/
@[simp] theorem homeomorphFundamentalGroupEquiv_symm_loop
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) (x : X) (γ : Path (f x) (f x)) :
    (homeomorphFundamentalGroupEquiv f x).symm (FundamentalGroup.fromPath (.mk γ)) =
      FundamentalGroup.fromPath (.mk ((γ.map f.symm.continuous).cast
        (f.symm_apply_apply x).symm (f.symm_apply_apply x).symm)) :=
  FundamentalGroup.mapOfEq_apply ⟨f.symm, f.symm.continuous⟩ (f.symm_apply_apply x) γ

/-- The based fundamental-group automorphism induced by an actual homeomorphism
and an actual path from the original basepoint to its image. -/
def basedHomeomorphFundamentalGroupEquiv {X : Type*} [TopologicalSpace X]
    (f : X ≃ₜ X) (x : X) (c : Path x (f x)) :
    FundamentalGroup X x ≃* FundamentalGroup X x :=
  (homeomorphFundamentalGroupEquiv f x).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPath c.symm)

/-- Exact actual loop formula, in the requested connector–mapped-loop–reverse
connector path order. No sign convention is supplied by an assumed field. -/
@[simp] theorem basedHomeomorphFundamentalGroupEquiv_loop
    {X : Type*} [TopologicalSpace X]
    (f : X ≃ₜ X) (x : X) (c : Path x (f x)) (γ : Path x x) :
    basedHomeomorphFundamentalGroupEquiv f x c (FundamentalGroup.fromPath (.mk γ)) =
      FundamentalGroup.fromPath (.mk ((c.trans (γ.map f.continuous)).trans c.symm)) := by
  change ((Path.Homotopic.Quotient.mk c.symm.symm).trans
    ((Path.Homotopic.Quotient.mk (γ.map f.continuous)).trans
      (Path.Homotopic.Quotient.mk c.symm))) = _
  rw [Path.symm_symm, ← Path.Homotopic.Quotient.trans_assoc,
    ← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_trans]

/-- Exact inverse-loop formula: conjugate by the reversed actual connector,
apply the actual inverse homeomorphism, then cast its source back to x.
Thus the inverse also retains the mapped reversed-connector construction. -/
@[simp] theorem basedHomeomorphFundamentalGroupEquiv_symm_loop
    {X : Type*} [TopologicalSpace X]
    (f : X ≃ₜ X) (x : X) (c : Path x (f x)) (γ : Path x x) :
    (basedHomeomorphFundamentalGroupEquiv f x c).symm
      (FundamentalGroup.fromPath (.mk γ)) =
        FundamentalGroup.fromPath (.mk
          ((((c.symm.trans γ).trans c).map f.symm.continuous).cast
            (f.symm_apply_apply x).symm (f.symm_apply_apply x).symm)) := by
  have hb : (FundamentalGroup.fundamentalGroupMulEquivOfPath c.symm).symm
      (FundamentalGroup.fromPath (.mk γ)) =
        FundamentalGroup.fromPath (.mk ((c.symm.trans γ).trans c)) := by
    change (Path.Homotopic.Quotient.mk c.symm).trans
      ((Path.Homotopic.Quotient.mk γ).trans (Path.Homotopic.Quotient.mk c.symm.symm)) = _
    rw [Path.symm_symm, ← Path.Homotopic.Quotient.trans_assoc,
      ← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_trans]
  change (homeomorphFundamentalGroupEquiv f x).symm
    ((FundamentalGroup.fundamentalGroupMulEquivOfPath c.symm).symm
      (FundamentalGroup.fromPath (.mk γ))) = _
  rw [hb, homeomorphFundamentalGroupEquiv_symm_loop]

end Markov
