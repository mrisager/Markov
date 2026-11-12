import Markov.CutoffArcs

/-! Finite arithmetic indices for actual cutoff gaps. A consecutive pair
is determined by its left endpoint, so the number of gap indices is
quadratic in the cutoff. No count of geometric connected components is
assumed in this module. -/

noncomputable section
namespace Markov

/-- An actual cutoff slope has at most one consecutive right neighbor. -/
theorem consecutiveCutoffSlopes_right_unique (H : ℕ) (u v w : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H u v) (h' : ConsecutiveCutoffSlopes H u w) : v = w := by
  have hdv := (consecutiveCutoffSlopes_det_and_denominator_sum H u v h).1
  have hdw := (consecutiveCutoffSlopes_det_and_denominator_sum H u w h').1
  rcases h with ⟨_, hv, huv, hno⟩
  rcases h' with ⟨_, hw, huw, hno'⟩
  have hvw : intDet v w = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hwv : 0 < intDet w v := by dsimp [intDet] at *; nlinarith
      exact hno w hw ⟨huw, hwv⟩
    · exact hno' v hv ⟨huv, hgt⟩
  have hcoord1 : w.1 = intDet u w * v.1 - intDet v w * u.1 := by
    dsimp [intDet] at *
    linear_combination -w.1 * hdv
  have hcoord2 : w.2 = intDet u w * v.2 - intDet v w * u.2 := by
    dsimp [intDet] at *
    linear_combination -w.2 * hdv
  apply Prod.ext
  · simpa only [hdw, hvw, one_mul, zero_mul, sub_zero] using hcoord1.symm
  · simpa only [hdw, hvw, one_mul, zero_mul, sub_zero] using hcoord2.symm

/-- All actual consecutive pairs in the finite canonical denominator cutoff. -/
def cutoffGapPairs (H : ℕ) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) := by
  classical
  exact ((cutoffSlopesUpTo H).product (cutoffSlopesUpTo H)).filter
    (fun uv => ConsecutiveCutoffSlopes H uv.1 uv.2)

theorem mem_cutoffGapPairs (H : ℕ) (u v : ℤ × ℤ) :
    (u, v) ∈ cutoffGapPairs H ↔ ConsecutiveCutoffSlopes H u v := by
  classical
  simp only [cutoffGapPairs, Finset.mem_filter, Finset.product_eq_sprod,
    Finset.mem_product]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.1, h.2.1⟩, h⟩⟩

/-- Count the consecutive pairs by their distinct left endpoints. -/
theorem cutoffGapPairs_card_le (H : ℕ) :
    (cutoffGapPairs H).card ≤ (cutoffSlopesUpTo H).card := by
  classical
  refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
  · intro uv huv
    exact ((mem_cutoffGapPairs H uv.1 uv.2).mp huv).1
  · intro uv huv wz hwz heq
    apply Prod.ext heq
    apply consecutiveCutoffSlopes_right_unique H uv.1 uv.2 wz.2
      ((mem_cutoffGapPairs H uv.1 uv.2).mp huv)
    rw [heq]
    exact (mem_cutoffGapPairs H wz.1 wz.2).mp hwz

/-- The canonical cutoff is a subset of the actual full primitive cutoff. -/
theorem cutoffSlopesUpTo_card_le_primitiveDirectionsUpTo (H : ℕ) :
    (cutoffSlopesUpTo H).card ≤ (primitiveDirectionsUpTo H).card := by
  classical
  exact Finset.card_le_card (fun u hu => cutoffSlope_mem_primitiveDirectionsUpTo H u hu)

/-- A quadratic bound for the canonical primitive denominator cutoff. -/
theorem cutoffSlopesUpTo_card_le (H : ℕ) :
    (cutoffSlopesUpTo H).card ≤ (2 * H + 1) ^ 2 :=
  (cutoffSlopesUpTo_card_le_primitiveDirectionsUpTo H).trans
    (primitiveDirectionsUpTo_card_le H)

/-- The finite arithmetic gap pairs have a quadratic count. -/
theorem cutoffGapPairs_card_le_quadratic (H : ℕ) :
    (cutoffGapPairs H).card ≤ (2 * H + 1) ^ 2 :=
  (cutoffGapPairs_card_le H).trans (cutoffSlopesUpTo_card_le H)

/-- Arithmetic indices for the actual cutoff gaps in all eight signed sectors. -/
def signedGapIndices (H : ℕ) : Finset (Fin 8 × ((ℤ × ℤ) × (ℤ × ℤ))) :=
  Finset.univ.product (cutoffGapPairs H)

theorem mem_signedGapIndices (H : ℕ) (k : Fin 8) (u v : ℤ × ℤ) :
    (k, (u, v)) ∈ signedGapIndices H ↔ ConsecutiveCutoffSlopes H u v := by
  classical
  simp only [signedGapIndices, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_univ, true_and, mem_cutoffGapPairs]

/-- The signed index count is eight times the canonical gap-pair count. -/
theorem signedGapIndices_card (H : ℕ) :
    (signedGapIndices H).card = 8 * (cutoffGapPairs H).card := by
  simp [signedGapIndices]

/-- Signed arithmetic gap indices are bounded by eight times the cutoff size. -/
theorem signedGapIndices_card_le_cutoffSlopes (H : ℕ) :
    (signedGapIndices H).card ≤ 8 * (cutoffSlopesUpTo H).card := by
  rw [signedGapIndices_card]
  exact Nat.mul_le_mul_left 8 (cutoffGapPairs_card_le H)

/-- The signed arithmetic gap indices have a quadratic count. -/
theorem signedGapIndices_card_le (H : ℕ) :
    (signedGapIndices H).card ≤ 8 * (2 * H + 1) ^ 2 := by
  rw [signedGapIndices_card]
  exact Nat.mul_le_mul_left 8 (cutoffGapPairs_card_le_quadratic H)

end Markov
