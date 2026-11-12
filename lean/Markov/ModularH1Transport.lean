import Markov.ModularTraceSingularH1
import Markov.PaperPrimitiveHolonomy
import Markov.SingularBasedLoopBoundary

noncomputable section
open scoped MatrixGroups
open CategoryTheory
namespace Markov

theorem singularLoopClass_conjugate (X : Type) [TopologicalSpace X]
    {x y : X} (α : Path x y) (γ : Path y y) :
    singularLoopClass X ((α.trans γ).trans α.symm) = singularLoopClass X γ := by
  let K := integralSingularChainComplex X
  let c := singularBasedLoopTwoChain X α γ α
  have hc : singularLoopCycle X ((α.trans γ).trans α.symm) -
      singularLoopCycle X γ = K.toCycles 2 1 c := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles 1)).mp inferInstance
    rw [map_sub, singularLoopCycle_iCycles, singularLoopCycle_iCycles]
    change _ = (K.toCycles 2 1 ≫ K.iCycles 1) c
    rw [K.toCycles_i]
    dsimp only [c]
    rw [singularBasedLoopTwoChain_boundary]
    abel
  apply sub_eq_zero.mp
  change K.homologyπ 1 (singularLoopCycle X ((α.trans γ).trans α.symm)) -
    K.homologyπ 1 (singularLoopCycle X γ) = 0
  rw [← map_sub, hc]
  change (K.toCycles 2 1 ≫ K.homologyπ 1) c = 0
  rw [K.toCycles_comp_homologyπ]
  rfl


/-- Every actual path to a forward deck endpoint has its own singular H1 marking. -/
theorem modularTraceSingularH1Equiv_projectedPath (z : UpperHalfPlane)
    (g : modularTraceSubgroup) (γ : Path z (g • z)) :
    modularTraceSingularH1Equiv z (singularLoopClass ModularTraceQuotient
      ((γ.map modularTraceQuotientMk_continuous).cast rfl
        (modularTraceQuotientMk_smul g z).symm)) =
      (paperTraceAbelianizationCoordinates g).toAdd := by
  rw [modularTraceSingularH1Equiv_loop, modularTraceMarkedCoordinates_projectedPath]

/-- An actual change-of-basepoint lift, with translated return segment. -/
def modularTraceForwardTransportPath (z w : UpperHalfPlane)
    (g : modularTraceSubgroup) (α : Path z w) : Path z (g • z) :=
  (α.trans (PathConnectedSpace.somePath w (g • w))).trans
    (α.map (modularTraceSubgroup_isometry g).continuous).symm

/-- Its projection is exactly the conjugation of the original actual forward loop. -/
theorem modularTraceForwardTransportPath_projected (z w : UpperHalfPlane)
    (g : modularTraceSubgroup) (α : Path z w) :
    (((modularTraceForwardTransportPath z w g α).map modularTraceQuotientMk_continuous).cast
      rfl (modularTraceQuotientMk_smul g z).symm) =
      (((α.map modularTraceQuotientMk_continuous).trans (modularTraceForwardLoop w g)).trans
        (α.map modularTraceQuotientMk_continuous).symm) := by
  ext t
  simp only [modularTraceForwardTransportPath, Path.cast_coe, Path.map_coe,
    Function.comp_apply, Path.trans_apply, Path.symm_apply,
    modularTraceForwardLoop_apply]
  split_ifs <;> simp only [modularTraceQuotientMk_smul]

/-- Forward deck loops at different actual lifts represent the same actual singular class. -/
theorem modularTraceForwardLoop_singularClass_basepoint (z w : UpperHalfPlane)
    (g : modularTraceSubgroup) :
    singularLoopClass ModularTraceQuotient (modularTraceForwardLoop z g) =
      singularLoopClass ModularTraceQuotient (modularTraceForwardLoop w g) := by
  let α := PathConnectedSpace.somePath z w
  have ht := modularTraceForwardTransportPath_projected z w g α
  have hc : modularTraceSingularH1Equiv z
      (singularLoopClass ModularTraceQuotient (modularTraceForwardLoop w g)) =
        (paperTraceAbelianizationCoordinates g).toAdd := by
    rw [← singularLoopClass_conjugate ModularTraceQuotient
      (α.map modularTraceQuotientMk_continuous) (modularTraceForwardLoop w g), ← ht]
    exact modularTraceSingularH1Equiv_projectedPath z g
      (modularTraceForwardTransportPath z w g α)
  apply (modularTraceSingularH1Equiv z).injective
  rw [modularTraceSingularH1Equiv_forwardLoop, hc]

/-- The genuine original positive A/B singular-H1 marking is independent of the lift. -/
theorem modularTraceSingularH1Equiv_basepoint (z w : UpperHalfPlane) :
    modularTraceSingularH1Equiv z = modularTraceSingularH1Equiv w := by
  apply AddEquiv.ext
  intro c
  let a := singularLoopClass ModularTraceQuotient
    (modularTraceForwardLoop z (paperTraceFreeGroupBasis 0))
  let b := singularLoopClass ModularTraceQuotient
    (modularTraceForwardLoop z (paperTraceFreeGroupBasis 1))
  have hza : modularTraceSingularH1Equiv z a = ((1, 0) : ℤ × ℤ) :=
    modularTraceSingularH1Equiv_basis_zero z
  have hzb : modularTraceSingularH1Equiv z b = ((0, 1) : ℤ × ℤ) :=
    modularTraceSingularH1Equiv_basis_one z
  have hwa : modularTraceSingularH1Equiv w a = ((1, 0) : ℤ × ℤ) := by
    dsimp only [a]
    rw [modularTraceForwardLoop_singularClass_basepoint z w]
    exact modularTraceSingularH1Equiv_basis_zero w
  have hwb : modularTraceSingularH1Equiv w b = ((0, 1) : ℤ × ℤ) := by
    dsimp only [b]
    rw [modularTraceForwardLoop_singularClass_basepoint z w]
    exact modularTraceSingularH1Equiv_basis_one w
  have hd : c = (modularTraceSingularH1Equiv z c).1 • a +
      (modularTraceSingularH1Equiv z c).2 • b := by
    apply (modularTraceSingularH1Equiv z).injective
    rw [map_add, map_zsmul, map_zsmul, hza, hzb]
    ext <;> simp
  conv_lhs => rw [hd]
  conv_rhs => rw [hd]
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, map_zsmul,
    hza, hzb, hwa, hwb]

/-- The single global marking uses the literal upper-half-plane point I. -/
def modularTraceFixedSingularH1Equiv :
    integralSingularH1 ModularTraceQuotient ≃+ (ℤ × ℤ) :=
  modularTraceSingularH1Equiv UpperHalfPlane.I

/-- A loop at any actual quotient basepoint is read in the single fixed-I marking. -/
theorem modularTraceFixedSingularH1Equiv_loop (z : UpperHalfPlane)
    (γ : Path (modularTraceQuotientMk z) (modularTraceQuotientMk z)) :
    modularTraceFixedSingularH1Equiv (singularLoopClass ModularTraceQuotient γ) =
      (modularTraceMarkedCoordinates z (FundamentalGroup.fromPath (.mk γ))).toAdd := by
  rw [modularTraceFixedSingularH1Equiv,
    modularTraceSingularH1Equiv_basepoint UpperHalfPlane.I z,
    modularTraceSingularH1Equiv_loop]

/-- Every actual projected forward path has its coordinates in the fixed-I marking. -/
theorem modularTraceFixedSingularH1Equiv_projectedPath (z : UpperHalfPlane)
    (g : modularTraceSubgroup) (γ : Path z (g • z)) :
    modularTraceFixedSingularH1Equiv (singularLoopClass ModularTraceQuotient
      ((γ.map modularTraceQuotientMk_continuous).cast rfl
        (modularTraceQuotientMk_smul g z).symm)) =
      (paperTraceAbelianizationCoordinates g).toAdd := by
  rw [modularTraceFixedSingularH1Equiv,
    modularTraceSingularH1Equiv_basepoint UpperHalfPlane.I z,
    modularTraceSingularH1Equiv_projectedPath]

/-- The actual full-period hyperbolic axis loop has its actual deck coordinates
in the single fixed-I singular-H1 marking. No least-period claim is needed. -/
theorem modularClosedGeodesicLoop_fixedSingularCoordinates (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) :
    modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient (modularClosedGeodesicLoop g hg)) =
        (paperTraceAbelianizationCoordinates g).toAdd := by
  have he :
      (((modularHyperbolicAxisSegment g hg).map modularTraceQuotientMk_continuous).cast rfl
        (modularTraceQuotientMk_smul g (modularHyperbolicAxis g hg 0)).symm) =
      modularClosedGeodesicLoop g hg := by
    ext t
    rfl
  rw [← he]
  exact modularTraceFixedSingularH1Equiv_projectedPath (modularHyperbolicAxis g hg 0)
    g (modularHyperbolicAxisSegment g hg)

/-- The actual canonical primitive axis-period loop has exactly p in the
single fixed-I actual singular-H1 marking, for every signed quadrant. -/
theorem paperPrimitiveClosedGeodesicLoop_fixedSingularCoordinates
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    modularTraceFixedSingularH1Equiv (singularLoopClass ModularTraceQuotient
      (modularClosedGeodesicLoop (paperPrimitiveHolonomy k p hp)
        (paperPrimitiveHolonomy_hyperbolic k p hp))) = p := by
  rw [modularClosedGeodesicLoop_fixedSingularCoordinates,
    paperPrimitiveHolonomy_coordinates]
  rfl

end Markov

