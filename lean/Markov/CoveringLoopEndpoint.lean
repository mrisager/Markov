import Mathlib.Topology.Homotopy.Lifting

/-! Endpoints of actual lifted loop classes for a simply connected covering.
No group multiplication, deck-group identification or homology calculation is
built into this equivalence. The endpoint is the library's actual monodromy. -/

noncomputable section
namespace Markov

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- The actual endpoint in the fibre obtained by lifting a based loop class
through a covering map from a specified point of its total space. -/
def coveringLoopEndpoint (cov : IsCoveringMap p) (e0 : E) :
    Path.Homotopic.Quotient (p e0) (p e0) → (p ⁻¹' {p e0}) :=
  fun γ => cov.monodromy γ ⟨e0, rfl⟩

@[simp] theorem coveringLoopEndpoint_mk_val (cov : IsCoveringMap p) (e0 : E)
    (γ : Path (p e0) (p e0)) :
    (coveringLoopEndpoint cov e0 (.mk γ) : E) = cov.liftPath γ e0 γ.source 1 :=
  rfl

/-- Projecting a path upstairs and viewing its projection as a loop gives
its actual terminal lift back, including the stated equality of fibre points. -/
theorem coveringLoopEndpoint_projectedPath (cov : IsCoveringMap p)
    {e0 y : E} (γ : Path e0 y) (hy : p y = p e0) :
    coveringLoopEndpoint cov e0 (.mk ((γ.map cov.continuous).cast rfl hy.symm)) =
      ⟨y, hy⟩ := by
  let δ : Path (p e0) (p e0) := (γ.map cov.continuous).cast rfl hy.symm
  have hlift : γ.toContinuousMap = cov.liftPath δ e0 δ.source := by
    apply (cov.eq_liftPath_iff' δ.source).mpr
    exact ⟨rfl, γ.source⟩
  apply Subtype.ext
  change cov.liftPath δ e0 δ.source 1 = y
  rw [← hlift]
  exact γ.target

/-- Path connectedness of the actual total space suffices to reach every
point of the fibre by a lifted loop class. -/
theorem coveringLoopEndpoint_surjective [PathConnectedSpace E]
    (cov : IsCoveringMap p) (e0 : E) :
    Function.Surjective (coveringLoopEndpoint cov e0) := by
  intro y
  let γ := PathConnectedSpace.somePath e0 y.val
  exact ⟨.mk ((γ.map cov.continuous).cast rfl y.property.symm),
    coveringLoopEndpoint_projectedPath cov γ y.property⟩

/-- Simple connectedness of the actual total space makes the lifted-loop
endpoint determine the original loop homotopy class. -/
theorem coveringLoopEndpoint_injective [SimplyConnectedSpace E]
    (cov : IsCoveringMap p) (e0 : E) :
    Function.Injective (coveringLoopEndpoint cov e0) := by
  intro γ δ h
  induction γ using Path.Homotopic.Quotient.ind with | mk γ =>
  induction δ using Path.Homotopic.Quotient.ind with | mk δ =>
  have hend : cov.liftPath γ e0 γ.source 1 = cov.liftPath δ e0 δ.source 1 :=
    congrArg Subtype.val h
  let Γ : Path e0 (cov.liftPath γ e0 γ.source 1) :=
    ⟨cov.liftPath γ e0 γ.source, cov.liftPath_zero γ e0 γ.source, rfl⟩
  let Δ : Path e0 (cov.liftPath γ e0 γ.source 1) :=
    ⟨cov.liftPath δ e0 δ.source, cov.liftPath_zero δ e0 δ.source, hend.symm⟩
  have hhom := (SimplyConnectedSpace.paths_homotopic Γ Δ).map ⟨p, cov.continuous⟩
  have hΓ : (Γ.map cov.continuous).toContinuousMap = γ.toContinuousMap := by
    ext t
    exact congr_fun (cov.liftPath_lifts γ e0 γ.source) t
  have hΔ : (Δ.map cov.continuous).toContinuousMap = δ.toContinuousMap := by
    ext t
    exact congr_fun (cov.liftPath_lifts δ e0 δ.source) t
  apply Path.Homotopic.Quotient.eq.mpr
  change γ.toContinuousMap.HomotopicRel δ.toContinuousMap {0, 1}
  change (Γ.map cov.continuous).toContinuousMap.HomotopicRel
    (Δ.map cov.continuous).toContinuousMap {0, 1} at hhom
  rwa [hΓ, hΔ] at hhom

/-- The actual loop-class endpoint equivalence for a simply connected
covering total space. Its map is precisely library monodromy at `e0`. -/
def coveringLoopEndpointEquiv [SimplyConnectedSpace E]
    (cov : IsCoveringMap p) (e0 : E) :
    Path.Homotopic.Quotient (p e0) (p e0) ≃ (p ⁻¹' {p e0}) :=
  Equiv.ofBijective (coveringLoopEndpoint cov e0)
    ⟨coveringLoopEndpoint_injective cov e0, coveringLoopEndpoint_surjective cov e0⟩

@[simp] theorem coveringLoopEndpointEquiv_apply [SimplyConnectedSpace E]
    (cov : IsCoveringMap p) (e0 : E)
    (γ : Path.Homotopic.Quotient (p e0) (p e0)) :
    coveringLoopEndpointEquiv cov e0 γ = cov.monodromy γ ⟨e0, rfl⟩ :=
  rfl

/-- A version on the library's fundamental-group type, as a plain type
 equivalence only. Its group multiplication convention is left untouched. -/
def coveringFundamentalGroupEndpointEquiv [SimplyConnectedSpace E]
    (cov : IsCoveringMap p) (e0 : E) :
    FundamentalGroup X (p e0) ≃ (p ⁻¹' {p e0}) :=
  coveringLoopEndpointEquiv cov e0

end Markov
