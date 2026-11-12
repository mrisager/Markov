import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic

/-! Actual circle descent from an exact integer-period equality criterion.
The criterion is an explicit hypothesis; its actual canonical-axis discharge is
separate. Descent uses the literal quotient, and compactness proves closedness. -/

noncomputable section
open Set Topology
universe u
namespace Markov

variable {X : Type u}

/-- The exact pair-equality criterion proves actual periodicity. -/
theorem integerPeriodEquality_periodic (L : ℝ) (q : ℝ → X)
    (heq : ∀ s t : ℝ, q s=q t ↔ ∃ n : ℤ, s-t=(n:ℝ)*L) : Function.Periodic q L := by
  intro t
  apply (heq (t+L) t).mpr
  exact ⟨1,by push_cast; ring⟩

variable [TopologicalSpace X]

/-- The actual continuous map out of the literal circle quotient. -/
def integerPeriodCircleMap (L : ℝ) (q : ℝ → X) (hq : Continuous q)
    (heq : ∀ s t : ℝ, q s=q t ↔ ∃ n : ℤ, s-t=(n:ℝ)*L) : C(AddCircle L,X) where
  toFun := (integerPeriodEquality_periodic L q heq).lift
  continuous_toFun := continuous_quot_lift _ hq

/-- Every real representative has precisely its original displayed curve value. -/
@[simp] theorem integerPeriodCircleMap_coe (L : ℝ) (q : ℝ → X) (hq : Continuous q)
    (heq : ∀ s t : ℝ, q s=q t ↔ ∃ n : ℤ, s-t=(n:ℝ)*L) (t : ℝ) :
    integerPeriodCircleMap L q hq heq (t : AddCircle L) = q t := rfl

/-- The exact pair-equality criterion makes the actual quotient map injective. -/
theorem integerPeriodCircleMap_injective (L : ℝ) (q : ℝ → X) (hq : Continuous q)
    (heq : ∀ s t : ℝ, q s=q t ↔ ∃ n : ℤ, s-t=(n:ℝ)*L) :
    Function.Injective (integerPeriodCircleMap L q hq heq) := by
  intro x y h
  obtain ⟨s,rfl⟩ := Quotient.exists_rep x
  obtain ⟨t,rfl⟩ := Quotient.exists_rep y
  change q s=q t at h
  obtain ⟨n,hn⟩ := (heq s t).mp h
  apply sub_eq_zero.mp
  change ((s-t : ℝ) : AddCircle L)=0
  apply (AddCircle.coe_eq_zero_iff (p:=L)).mpr
  refine ⟨n,?_⟩
  simpa only [zsmul_eq_mul] using hn.symm

/-- Positive period and a Hausdorff target turn the actual quotient map into an
actual closed embedding, by compactness of AddCircle L. -/
theorem integerPeriodCircleMap_isClosedEmbedding [T2Space X]
    (L : ℝ) (hL : 0<L) (q : ℝ → X) (hq : Continuous q)
    (heq : ∀ s t : ℝ, q s=q t ↔ ∃ n : ℤ, s-t=(n:ℝ)*L) :
    IsClosedEmbedding (integerPeriodCircleMap L q hq heq) := by
  letI : Fact (0<L) := ⟨hL⟩
  exact (integerPeriodCircleMap L q hq heq).continuous.isClosedEmbedding
    (integerPeriodCircleMap_injective L q hq heq)

/-- The image is exactly the original full real-curve range. -/
theorem integerPeriodCircleMap_range (L : ℝ) (q : ℝ → X) (hq : Continuous q)
    (heq : ∀ s t : ℝ, q s=q t ↔ ∃ n : ℤ, s-t=(n:ℝ)*L) :
    range (integerPeriodCircleMap L q hq heq) = range q := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨t,rfl⟩ := Quotient.exists_rep x
    exact ⟨t,rfl⟩
  · rintro ⟨t,rfl⟩
    exact ⟨(t : AddCircle L),rfl⟩

end Markov
