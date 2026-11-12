import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Real.Basic

/-! Constructed increasing tables of an actual finite real cut set, with both
endpoints and cut-free consecutive gaps. No ordered-table witness is assumed. -/

noncomputable section
open Set
namespace Markov

/-- The literal finite cut set with its two interval endpoints adjoined. -/
def finiteRealCutPoints (a b : ℝ) (S : Set ℝ) (hS : S.Finite) : Finset ℝ := by
  classical
  exact insert a (insert b hS.toFinset)

@[simp] theorem mem_finiteRealCutPoints (a b : ℝ) (S : Set ℝ) (hS : S.Finite) (x : ℝ) :
    x ∈ finiteRealCutPoints a b S hS ↔ x = a ∨ x = b ∨ x ∈ S := by
  classical
  simp [finiteRealCutPoints]

theorem finiteRealCutPoints_card_pos (a b : ℝ) (S : Set ℝ) (hS : S.Finite) :
    0 < (finiteRealCutPoints a b S hS).card := by
  apply Finset.card_pos.mpr
  exact ⟨a, (mem_finiteRealCutPoints a b S hS a).mpr (Or.inl rfl)⟩

/-- This is the actual increasing enumeration, constructed by finite sorting. -/
def finiteRealCutTable (a b : ℝ) (S : Set ℝ) (hS : S.Finite) :
    Fin (finiteRealCutPoints a b S hS).card ↪o ℝ :=
  (finiteRealCutPoints a b S hS).orderEmbOfFin rfl

theorem finiteRealCutTable_strictMono (a b : ℝ) (S : Set ℝ) (hS : S.Finite) :
    StrictMono (finiteRealCutTable a b S hS) :=
  (finiteRealCutTable a b S hS).strictMono

theorem finiteRealCutTable_range (a b : ℝ) (S : Set ℝ) (hS : S.Finite) :
    range (finiteRealCutTable a b S hS) = (finiteRealCutPoints a b S hS : Set ℝ) :=
  Finset.range_orderEmbOfFin _ rfl

theorem finiteRealCutTable_bounds (a b : ℝ) (hab : a < b)
    (S : Set ℝ) (hS : S.Finite) (hbound : S ⊆ Ioo a b)
    (i : Fin (finiteRealCutPoints a b S hS).card) :
    a ≤ finiteRealCutTable a b S hS i ∧ finiteRealCutTable a b S hS i ≤ b := by
  have hi : finiteRealCutTable a b S hS i ∈ finiteRealCutPoints a b S hS := by
    exact Finset.orderEmbOfFin_mem _ rfl i
  rcases (mem_finiteRealCutPoints a b S hS _).mp hi with ha | hb | hmem
  · rw [ha]; exact ⟨le_rfl, hab.le⟩
  · rw [hb]; exact ⟨hab.le, le_rfl⟩
  · exact ⟨(hbound hmem).1.le, (hbound hmem).2.le⟩

/-- The first constructed table point is literally the left endpoint. -/
theorem finiteRealCutTable_first (a b : ℝ) (hab : a < b)
    (S : Set ℝ) (hS : S.Finite) (hbound : S ⊆ Ioo a b) :
    finiteRealCutTable a b S hS ⟨0, finiteRealCutPoints_card_pos a b S hS⟩ = a := by
  have ha : a ∈ range (finiteRealCutTable a b S hS) := by
    rw [finiteRealCutTable_range]
    exact (mem_finiteRealCutPoints a b S hS a).mpr (Or.inl rfl)
  obtain ⟨j, hj⟩ := ha
  apply le_antisymm
  · have hle : (⟨0, finiteRealCutPoints_card_pos a b S hS⟩ :
        Fin (finiteRealCutPoints a b S hS).card) ≤ j := Nat.zero_le _
    exact ((finiteRealCutTable a b S hS).monotone hle).trans_eq hj
  · exact (finiteRealCutTable_bounds a b hab S hS hbound _).1

/-- The last constructed table point is literally the right endpoint. -/
theorem finiteRealCutTable_last (a b : ℝ) (hab : a < b)
    (S : Set ℝ) (hS : S.Finite) (hbound : S ⊆ Ioo a b) :
    finiteRealCutTable a b S hS
      ⟨(finiteRealCutPoints a b S hS).card - 1,
        Nat.sub_lt (finiteRealCutPoints_card_pos a b S hS) (by decide)⟩ = b := by
  have hb : b ∈ range (finiteRealCutTable a b S hS) := by
    rw [finiteRealCutTable_range]
    exact (mem_finiteRealCutPoints a b S hS b).mpr (Or.inr (Or.inl rfl))
  obtain ⟨j, hj⟩ := hb
  apply le_antisymm
  · exact (finiteRealCutTable_bounds a b hab S hS hbound _).2
  · have hle : j ≤ (⟨(finiteRealCutPoints a b S hS).card - 1,
        Nat.sub_lt (finiteRealCutPoints_card_pos a b S hS) (by decide)⟩ :
        Fin (finiteRealCutPoints a b S hS).card) := by
      have hjlt := j.isLt
      change j.val ≤ (finiteRealCutPoints a b S hS).card - 1
      omega
    exact hj.symm.trans_le ((finiteRealCutTable a b S hS).monotone hle)

/-- Consecutive entries of the constructed enumeration contain no cut.
Consecutiveness refers to actual integer indices, not an assumed gap property. -/
theorem finiteRealCutTable_gap_not_mem (a b : ℝ) (S : Set ℝ) (hS : S.Finite)
    (i j : Fin (finiteRealCutPoints a b S hS).card) (hij : j.val = i.val + 1)
    (x : ℝ) (hx : x ∈ Ioo (finiteRealCutTable a b S hS i) (finiteRealCutTable a b S hS j)) :
    x ∉ S := by
  intro hmem
  have hxrange : x ∈ range (finiteRealCutTable a b S hS) := by
    rw [finiteRealCutTable_range]
    exact (mem_finiteRealCutPoints a b S hS x).mpr (Or.inr (Or.inr hmem))
  obtain ⟨k, hk⟩ := hxrange
  have hik : i < k := (finiteRealCutTable a b S hS).lt_iff_lt.mp (by rw [hk]; exact hx.1)
  have hkj : k < j := (finiteRealCutTable a b S hS).lt_iff_lt.mp (by rw [hk]; exact hx.2)
  change i.val < k.val at hik
  change k.val < j.val at hkj
  omega

end Markov
