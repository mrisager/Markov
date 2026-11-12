import Markov.TraceUnresolvedMonotone
import Markov.PrimitiveAngularSpacing
import Markov.TraceUnresolvedAngularWidth
import Markov.GlobalCutoffCount

/-! A finite-set counting core for unresolved primitive directions. Passing
to a coarser actual cutoff preserves each unresolved witness. If every
coarse component's actual normal neighborhood is narrower than primitive
angular spacing, distinct directions occupy distinct actual components.
The finite signed cutoff family then gives the bound `72 * h²`. -/

noncomputable section
open Set

namespace Markov

/-- A finite set of primitive unresolved directions is bounded by the
coarse component count whenever the actual normal neighborhoods are
narrower than the primitive angular-spacing threshold. -/
theorem traceUnresolved_finset_card_le_of_component_width
    (S : Finset (ℤ × ℤ)) (K H h η T L : ℝ)
    (hh : 1 ≤ h) (hhH : h ≤ H) (hT : 1 ≤ T)
    (hprimitive : ∀ d ∈ S, IsCoprime d.1 d.2)
    (hsize : ∀ d ∈ S, intEuclidean d ≤ T)
    (hunresolved : ∀ d ∈ S, IsTraceUnresolved d K H η)
    (hwidth : ∀ x ∈ traceUncutBoundary h,
      ∀ z z' : EuclideanSpace ℝ (Fin 2),
        z ∈ closedAngularNeighborhood
          (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary h) x)) η →
        z' ∈ closedAngularNeighborhood
          (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary h) x)) η →
        InnerProductGeometry.angle z z' ≤ L + 2 * η)
    (hsmall : L + 2 * η < 1 / T ^ 2) :
    (S.card : ℝ) ≤ 72 * h ^ 2 := by
  classical
  have hh0 : 0 ≤ h := le_trans (by norm_num) hh
  have hfloor : 1 ≤ ⌊h⌋₊ := (Nat.le_floor_iff hh0).mpr (by simpa using hh)
  have hwitness (d : S) : ∃ x ∈ traceUncutBoundary h,
      NormedSpace.normalize (euclideanIntDirection d.val) ∈
        closedAngularNeighborhood
          (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary h) x)) η :=
    ((hunresolved d.val d.property).mono_cutoff hhH).2.2
  choose x hx hmem using hwitness
  let f : S → cutoffComponentFamily traceBasis ⌊h⌋₊ := fun d =>
    ⟨connectedComponentIn (traceUncutBoundary h) (x d), by
      have hd := hx d
      rw [traceUncutBoundary_eq_natFloor h hh0] at hd ⊢
      exact connectedComponentIn_mem_cutoffComponentFamily traceBasis ⌊h⌋₊
        hfloor (x d) hd⟩
  have hinj : Function.Injective f := by
    intro d e hde
    have hcomp : connectedComponentIn (traceUncutBoundary h) (x d) =
        connectedComponentIn (traceUncutBoundary h) (x e) := congrArg Subtype.val hde
    have he := hmem e
    rw [← hcomp] at he
    apply Subtype.ext
    exact primitive_eq_of_angle_lt_inv_sq d.val e.val
      (hprimitive d.val d.property) (hprimitive e.val e.property) T hT
      (hsize d.val d.property) (hsize e.val e.property)
      ((hwidth (x d) (hx d) _ _ (hmem d) he).trans_lt hsmall)
  have hcard : S.card ≤ (cutoffComponentFamily traceBasis ⌊h⌋₊).card := by
    simpa using Fintype.card_le_of_injective f hinj
  have hfamily : (cutoffComponentFamily traceBasis ⌊h⌋₊).card ≤ 72 * ⌊h⌋₊ ^ 2 := by
    calc
      _ ≤ 8 * (2 * ⌊h⌋₊ + 1) ^ 2 := cutoffComponentFamily_card_le traceBasis ⌊h⌋₊
      _ ≤ 8 * (3 * ⌊h⌋₊) ^ 2 := by gcongr; omega
      _ = 72 * ⌊h⌋₊ ^ 2 := by ring
  have hnat : (S.card : ℝ) ≤ 72 * (⌊h⌋₊ : ℝ) ^ 2 := by
    exact_mod_cast hcard.trans hfamily
  exact hnat.trans (by gcongr; exact Nat.floor_le hh0)

/-- Fixed exponential constants give the finite-set coarse-cutoff bound
under the displayed angular-width inequality. The width hypothesis refers
to the actual closed normal neighborhoods of actual coarse components. -/
theorem traceUnresolved_finset_card_le_of_exp_width
    (M κ : ℝ) (S : Finset (ℤ × ℤ)) (K H h η T : ℝ)
    (hh : 1 ≤ h) (hhH : h ≤ H) (hT : 1 ≤ T)
    (hprimitive : ∀ d ∈ S, IsCoprime d.1 d.2)
    (hsize : ∀ d ∈ S, intEuclidean d ≤ T)
    (hunresolved : ∀ d ∈ S, IsTraceUnresolved d K H η)
    (hwidth : ∀ x ∈ traceUncutBoundary h,
      ∀ z z' : EuclideanSpace ℝ (Fin 2),
        z ∈ closedAngularNeighborhood
          (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary h) x)) η →
        z' ∈ closedAngularNeighborhood
          (normalsOn traceBasis (connectedComponentIn (traceUncutBoundary h) x)) η →
        InnerProductGeometry.angle z z' ≤ M * Real.exp (-(κ * h)) + 2 * η)
    (hsmall : M * Real.exp (-(κ * h)) + 2 * η < 1 / T ^ 2) :
    (S.card : ℝ) ≤ 72 * h ^ 2 :=
  traceUnresolved_finset_card_le_of_component_width S K H h η T
    (M * Real.exp (-(κ * h))) hh hhH hT hprimitive hsize hunresolved hwidth hsmall

/-- The proved exponential width of actual uncut-component normal
neighborhoods supplies uniform positive constants for the finite-set
count. No uniqueness of the original unresolved association is needed. -/
theorem traceUnresolved_finset_card_le_coarse_cutoff :
    ∃ M κ : ℝ, 0 < M ∧ 0 < κ ∧
      ∀ (S : Finset (ℤ × ℤ)) (K H h η T : ℝ),
        1 ≤ h → h ≤ H → 1 ≤ T →
        (∀ d ∈ S, IsCoprime d.1 d.2) →
        (∀ d ∈ S, intEuclidean d ≤ T) →
        (∀ d ∈ S, IsTraceUnresolved d K H η) →
        M * Real.exp (-(κ * h)) + 2 * η < 1 / T ^ 2 →
        (S.card : ℝ) ≤ 72 * h ^ 2 := by
  obtain ⟨M, κ, hM, hκ, hwidth⟩ :=
    traceUncutBoundary_component_angular_neighborhood_exp_width
  refine ⟨M, κ, hM, hκ, ?_⟩
  intro S K H h η T hh hhH hT hprimitive hsize hunresolved hsmall
  exact traceUnresolved_finset_card_le_of_exp_width M κ S K H h η T hh hhH hT
    hprimitive hsize hunresolved (fun x hx z z' hz hz' =>
      hwidth h hh x hx η z z' hz hz') hsmall

end Markov
