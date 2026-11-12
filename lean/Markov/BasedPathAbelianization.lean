import Markov.SingularHurewiczMap

/-! Explicit based-loop abelianization classes of paths using actual
connecting paths. These are algebraic pi1 abelianization classes, not a
replacement definition of singular H1 and not a Hurewicz inverse theorem. -/

noncomputable section
namespace Markov

variable (X : Type) [TopologicalSpace X] (x : X)

abbrev BasedLoopAbelianGroup := Additive (Abelianization (FundamentalGroup X x))

/-- An actual loop class in the actual pi1 abelianization. -/
def loopAbelianClass (c : Path.Homotopic.Quotient x x) : BasedLoopAbelianGroup X x :=
  Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath c))

theorem loopAbelianClass_trans (c d : Path.Homotopic.Quotient x x) :
    loopAbelianClass X x (c.trans d) = loopAbelianClass X x c + loopAbelianClass X x d := by
  have he : FundamentalGroup.fromPath (c.trans d) =
      FundamentalGroup.fromPath d * FundamentalGroup.fromPath c := rfl
  unfold loopAbelianClass
  rw [he, map_mul]
  change (Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath d)) : BasedLoopAbelianGroup X x) +
    Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath c)) =
    Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath c)) +
    Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath d))
  exact add_comm _ _

theorem loopAbelianClass_symm (c : Path.Homotopic.Quotient x x) :
    loopAbelianClass X x c.symm = -loopAbelianClass X x c := by
  have he : FundamentalGroup.fromPath c.symm = (FundamentalGroup.fromPath c)⁻¹ := rfl
  unfold loopAbelianClass
  rw [he, map_inv]
  rfl

variable (τ : ∀ y : X, Path x y)

/-- Close an actual path homotopy class using the specified actual connectors. -/
def basedPathLoopQuotient {a b : X} (p : Path.Homotopic.Quotient a b) :
    Path.Homotopic.Quotient x x :=
  ((Path.Homotopic.Quotient.mk (τ a)).trans p).trans
    (Path.Homotopic.Quotient.mk (τ b)).symm

theorem basedPathLoopQuotient_trans {a b c : X}
    (p : Path.Homotopic.Quotient a b) (q : Path.Homotopic.Quotient b c) :
    basedPathLoopQuotient X x τ (p.trans q) =
      (basedPathLoopQuotient X x τ p).trans (basedPathLoopQuotient X x τ q) := by
  let A := Path.Homotopic.Quotient.mk (τ a)
  let B := Path.Homotopic.Quotient.mk (τ b)
  let C := Path.Homotopic.Quotient.mk (τ c)
  change (A.trans (p.trans q)).trans C.symm =
    ((A.trans p).trans B.symm).trans ((B.trans q).trans C.symm)
  rw [Path.Homotopic.Quotient.trans_assoc (A.trans p) B.symm,
    Path.Homotopic.Quotient.trans_assoc B q C.symm,
    ← Path.Homotopic.Quotient.trans_assoc B.symm B,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
  simp only [Path.Homotopic.Quotient.trans_assoc]

/-- The actual closed-loop abelianization class assigned to an oriented path. -/
def basedPathAbelianization {a b : X} (γ : Path a b) : BasedLoopAbelianGroup X x :=
  loopAbelianClass X x (basedPathLoopQuotient X x τ (.mk γ))

theorem basedPathAbelianization_trans {a b c : X} (γ : Path a b) (δ : Path b c) :
    basedPathAbelianization X x τ (γ.trans δ) =
      basedPathAbelianization X x τ γ + basedPathAbelianization X x τ δ := by
  unfold basedPathAbelianization
  rw [Path.Homotopic.Quotient.mk_trans, basedPathLoopQuotient_trans, loopAbelianClass_trans]

theorem basedPathAbelianization_homotopic {a b : X} {γ δ : Path a b}
    (h : Path.Homotopic γ δ) :
    basedPathAbelianization X x τ γ = basedPathAbelianization X x τ δ := by
  unfold basedPathAbelianization
  rw [Path.Homotopic.Quotient.eq.mpr h]

theorem basedPathAbelianization_cast {a b a' b' : X} (γ : Path a b)
    (ha : a' = a) (hb : b' = b) :
    basedPathAbelianization X x τ (γ.cast ha hb) = basedPathAbelianization X x τ γ := by
  cases ha
  cases hb
  rfl

/-- Literal equality of continuous paths preserves the based class even
when their endpoint expressions need the proved source/target identifications. -/
theorem basedPathAbelianization_ext {a b c d : X} (γ : Path a b) (δ : Path c d)
    (h : γ.toContinuousMap = δ.toContinuousMap) :
    basedPathAbelianization X x τ γ = basedPathAbelianization X x τ δ := by
  have ha : a = c := by
    calc
      a = γ 0 := γ.source.symm
      _ = δ 0 := congrArg (fun f : C(unitInterval, X) => f 0) h
      _ = c := δ.source
  have hb : b = d := by
    calc
      b = γ 1 := γ.target.symm
      _ = δ 1 := congrArg (fun f : C(unitInterval, X) => f 1) h
      _ = d := δ.target
  cases ha
  cases hb
  have he : γ = δ := by
    ext t
    exact congrArg (fun f : C(unitInterval, X) => f t) h
  rw [he]

/-- Concatenation followed by an actual relative-endpoint homotopy gives
the expected sum relation in the actual loop-group abelianization. -/
theorem basedPathAbelianization_triangle {a b c : X}
    (γ01 : Path a b) (γ12 : Path b c) (γ02 : Path a c)
    (h : Path.Homotopic (γ01.trans γ12) γ02) :
    basedPathAbelianization X x τ γ01 + basedPathAbelianization X x τ γ12 =
      basedPathAbelianization X x τ γ02 := by
  rw [← basedPathAbelianization_trans]
  exact basedPathAbelianization_homotopic X x τ h

/-- For a loop already based at x the connector contributes only a
conjugation, which disappears in the actual abelianization. -/
theorem basedPathAbelianization_loop (γ : Path x x) :
    basedPathAbelianization X x τ γ = loopAbelianClass X x (.mk γ) := by
  unfold basedPathAbelianization basedPathLoopQuotient
  rw [loopAbelianClass_trans, loopAbelianClass_trans, loopAbelianClass_symm]
  abel

end Markov
