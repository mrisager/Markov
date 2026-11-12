import Markov.CutoffNeighbors
import Mathlib.Data.Finset.Max

/-! The actual finite primitive denominator cutoff brackets every
uncut canonical slope by consecutive cutoff slopes. The proof uses
finite order alone; it assumes no norm or surface correspondence. -/

noncomputable section
namespace Markov

/-- A point omitted by a finite ordered image and lying between two image
values lies between adjacent image values. Injectivity is unnecessary. -/
theorem finset_exists_adjacent_bracketing {α β : Type*} [LinearOrder β]
    (S : Finset α) (f : α → β) (t : β)
    (hleft : ∃ u ∈ S, f u < t) (hright : ∃ v ∈ S, t < f v)
    (havoid : ∀ w ∈ S, f w ≠ t) :
    ∃ u ∈ S, ∃ v ∈ S, f u < t ∧ t < f v ∧
      ∀ w ∈ S, ¬(f u < f w ∧ f w < f v) := by
  classical
  let L := S.filter (fun u => f u < t)
  let R := S.filter (fun v => t < f v)
  have hL : L.Nonempty := by
    obtain ⟨u, hu, hut⟩ := hleft
    exact ⟨u, Finset.mem_filter.mpr ⟨hu, hut⟩⟩
  have hR : R.Nonempty := by
    obtain ⟨v, hv, htv⟩ := hright
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, htv⟩⟩
  obtain ⟨u, hu, humax⟩ := Finset.exists_max_image L f hL
  obtain ⟨v, hv, hvmin⟩ := Finset.exists_min_image R f hR
  obtain ⟨huS, hut⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvS, htv⟩ := Finset.mem_filter.mp hv
  refine ⟨u, huS, v, hvS, hut, htv, ?_⟩
  intro w hw hmid
  by_cases hwt : f w < t
  · exact (not_lt_of_ge (humax w (Finset.mem_filter.mpr ⟨hw, hwt⟩))) hmid.1
  · have htw : t < f w :=
      lt_of_le_of_ne (le_of_not_gt hwt) (Ne.symm (havoid w hw))
    exact (not_lt_of_ge (hvmin w (Finset.mem_filter.mpr ⟨hw, htw⟩))) hmid.2

/-- The two endpoint slopes belong to every positive denominator cutoff. -/
theorem cutoffSlopesUpTo_endpoints_mem (H : ℕ) (hH : 1 ≤ H) :
    ((1, 0) : ℤ × ℤ) ∈ cutoffSlopesUpTo H ∧
      ((1, 1) : ℤ × ℤ) ∈ cutoffSlopesUpTo H := by
  have hH' : (1 : ℤ) ≤ H := by exact_mod_cast hH
  constructor
  · exact (mem_cutoffSlopesUpTo H (1, 0)).mpr
      ⟨by norm_num, by norm_num, by norm_num, hH', by norm_num⟩
  · exact (mem_cutoffSlopesUpTo H (1, 1)).mpr
      ⟨by norm_num, by norm_num, by norm_num, hH', by norm_num⟩

/-- Every uncut slope strictly between zero and one lies in a gap between
actual consecutive primitive cutoff slopes. No determinant hypothesis is
assumed: consecutiveness refers to absence of an intermediate cutoff slope. -/
theorem exists_consecutiveCutoffSlopes_bracketing (H : ℕ) (hH : 1 ≤ H)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (havoid : ∀ w ∈ cutoffSlopesUpTo H, cutoffSlope w ≠ t) :
    ∃ u v : ℤ × ℤ, ConsecutiveCutoffSlopes H u v ∧
      t ∈ Set.Ioo (cutoffSlope u) (cutoffSlope v) := by
  have hend := cutoffSlopesUpTo_endpoints_mem H hH
  have hleft : ∃ u ∈ cutoffSlopesUpTo H, cutoffSlope u < t := by
    exact ⟨(1, 0), hend.1, by simpa [cutoffSlope] using ht.1⟩
  have hright : ∃ v ∈ cutoffSlopesUpTo H, t < cutoffSlope v := by
    exact ⟨(1, 1), hend.2, by simpa [cutoffSlope] using ht.2⟩
  obtain ⟨u, hu, v, hv, hut, htv, hbetween⟩ :=
    finset_exists_adjacent_bracketing (cutoffSlopesUpTo H) cutoffSlope t hleft hright havoid
  refine ⟨u, v, (consecutiveCutoffSlopes_iff_slope H u v).mpr ?_, hut, htv⟩
  exact ⟨hu, hv, hut.trans htv, hbetween⟩

end Markov
