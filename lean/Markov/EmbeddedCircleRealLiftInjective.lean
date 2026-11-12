import Markov.EmbeddedCircleRealLift
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- Actual backward unit equivariance follows from the proved forward unit law. -/
theorem embeddedCircleRealLift_sub_one
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) (t : ℝ) :
    embeddedCircleRealLift q hq z hz (t-1) =
      (embeddedCircleRealLiftDeck q hq z hz)⁻¹ • embeddedCircleRealLift q hq z hz t := by
  have h := congrArg (fun w : UpperHalfPlane => (embeddedCircleRealLiftDeck q hq z hz)⁻¹ • w)
    (embeddedCircleRealLift_add_one q hq z hz (t-1))
  simpa only [sub_add_cancel, inv_smul_smul] using h.symm

/-- Full actual integer equivariance, for both positive and negative parameter shifts. -/
theorem embeddedCircleRealLift_add_int
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) (n : ℤ) (t : ℝ) :
    embeddedCircleRealLift q hq z hz (t+(n : ℝ)) =
      (embeddedCircleRealLiftDeck q hq z hz)^n • embeddedCircleRealLift q hq z hz t := by
  induction n using Int.induction_on generalizing t with
  | zero => simp only [Int.cast_zero, add_zero, zpow_zero, one_smul]
  | succ n ih =>
    rw [Int.cast_add, Int.cast_one, ← add_assoc, embeddedCircleRealLift_add_one, ih]
    rw [← mul_self_zpow, mul_smul]
  | pred n ih =>
    rw [Int.cast_sub, Int.cast_one, ← add_sub_assoc, embeddedCircleRealLift_sub_one, ih]
    have he : (embeddedCircleRealLiftDeck q hq z hz)^(-(n : ℤ)-1) =
        (embeddedCircleRealLiftDeck q hq z hz)⁻¹ * (embeddedCircleRealLiftDeck q hq z hz)^(-(n : ℤ)) := by
      rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one]
    rw [he, mul_smul]

/-- Exact actual self-identification criterion for the global real lift.
The integral shift must also have trivial actual deck power; freeness of the
proved actual subgroup action supplies the reverse implication from a fixed point. -/
theorem embeddedCircleRealLift_eq_iff_deck_power
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0) (s t : ℝ) :
    embeddedCircleRealLift q hq z hz s = embeddedCircleRealLift q hq z hz t ↔
      ∃ n : ℤ, s-t = (n : ℝ) ∧ (embeddedCircleRealLiftDeck q hq z hz)^n = 1 := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := embeddedCircleRealLift_eq_imp_integer q hq z hz h
    refine ⟨n, hn, ?_⟩
    have hs : s = t+(n : ℝ) := by linarith
    have hfix : (embeddedCircleRealLiftDeck q hq z hz)^n • embeddedCircleRealLift q hq z hz t =
        embeddedCircleRealLift q hq z hz t := by
      rw [← embeddedCircleRealLift_add_int, ← hs]
      exact h
    apply Subtype.ext
    exact modularTraceSubgroup_eq_one_of_fixed_point
      ((embeddedCircleRealLiftDeck q hq z hz)^n).val
      ((embeddedCircleRealLiftDeck q hq z hz)^n).property
      (embeddedCircleRealLift q hq z hz t) hfix
  · rintro ⟨n, hn, hpow⟩
    have hs : s = t+(n : ℝ) := by linarith
    rw [hs, embeddedCircleRealLift_add_int, hpow, one_smul]

/-- Infinite-order actual unit monodromy makes the full real lift injective.
The infinite-order hypothesis remains explicit; an arbitrary embedded
contractible circle can instead have a periodic lift. -/
theorem embeddedCircleRealLift_injective_of_infiniteOrder
    (q : NormalizedCircle → ModularTraceQuotient) (hq : Topology.IsClosedEmbedding q)
    (z : UpperHalfPlane) (hz : modularTraceQuotientMk z = q 0)
    (hD : ¬ IsOfFinOrder (embeddedCircleRealLiftDeck q hq z hz)) :
    Function.Injective (embeddedCircleRealLift q hq z hz) := by
  intro s t h
  obtain ⟨n, hn, hpow⟩ := (embeddedCircleRealLift_eq_iff_deck_power q hq z hz s t).mp h
  have he : (embeddedCircleRealLiftDeck q hq z hz)^n = (embeddedCircleRealLiftDeck q hq z hz)^(0 : ℤ) := by
    simpa only [zpow_zero] using hpow
  have hn0 : n = 0 := (injective_zpow_iff_not_isOfFinOrder.mpr hD) he
  rw [hn0, Int.cast_zero] at hn
  exact sub_eq_zero.mp hn

end Markov
