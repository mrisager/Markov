import Markov.SignedQuadrantWords
import Markov.CutoffNeighbors

/-! Original lattice height bounds for actual consecutive cutoff endpoints
in any of the eight signed sectors. The omitted mediant is strictly above
the cutoff, whereas the two endpoint heights sum to at most twice it. -/

namespace Markov

theorem intHeight_eq_first_of_canonical (p : ℤ × ℤ)
    (hp0 : 0 ≤ p.2) (hp1 : p.2 ≤ p.1) : intHeight p = (p.1 : ℝ) := by
  have hp0R : (0 : ℝ) ≤ p.2 := by exact_mod_cast hp0
  have hp1R : (p.2 : ℝ) ≤ p.1 := by exact_mod_cast hp1
  rw [intHeight, abs_of_nonneg (hp0R.trans hp1R), abs_of_nonneg hp0R,
    max_eq_left hp1R]

theorem inverseSignedSectorCoordinates_height_eq_first_of_cutoff
    (k : Fin 8) (H : ℕ) (p : ℤ × ℤ) (hp : p ∈ cutoffSlopesUpTo H) :
    intHeight (inverseSignedSectorCoordinates k p) = (p.1 : ℝ) := by
  obtain ⟨_, hp0, hp1, _, _⟩ := (mem_cutoffSlopesUpTo H p).mp hp
  rw [inverseSignedSectorCoordinates_height, intHeight_eq_first_of_canonical p hp0 hp1]

/-- Both actual signed endpoints have positive integral height bounded by
the cutoff. -/
theorem inverseSignedSectorCoordinates_cutoff_height_bounds
    (k : Fin 8) (H : ℕ) (p : ℤ × ℤ) (hp : p ∈ cutoffSlopesUpTo H) :
    1 ≤ intHeight (inverseSignedSectorCoordinates k p) ∧
      intHeight (inverseSignedSectorCoordinates k p) ≤ (H : ℝ) := by
  rw [inverseSignedSectorCoordinates_height_eq_first_of_cutoff k H p hp]
  obtain ⟨hp0, _, _, hpH, _⟩ := (mem_cutoffSlopesUpTo H p).mp hp
  constructor
  · have hp1 : (1 : ℤ) ≤ p.1 := by omega
    exact_mod_cast hp1
  · exact_mod_cast hpH

/-- The original mediant height is exactly the sum of the endpoint heights
throughout one closed signed sector. -/
theorem inverseSignedSectorCoordinates_height_add_eq_of_canonical
    (k : Fin 8) (u v : ℤ × ℤ)
    (hu0 : 0 ≤ u.2) (hu1 : u.2 ≤ u.1)
    (hv0 : 0 ≤ v.2) (hv1 : v.2 ≤ v.1) :
    intHeight (inverseSignedSectorCoordinates k u + inverseSignedSectorCoordinates k v) =
      intHeight (inverseSignedSectorCoordinates k u) +
        intHeight (inverseSignedSectorCoordinates k v) := by
  rw [inverseSignedSectorCoordinates_height_add,
    inverseSignedSectorCoordinates_height, inverseSignedSectorCoordinates_height,
    intHeight_eq_first_of_canonical u hu0 hu1,
    intHeight_eq_first_of_canonical v hv0 hv1,
    intHeight_eq_first_of_canonical (u + v)
      (add_nonneg hu0 hv0) (add_le_add hu1 hv1)]
  simp only [Prod.fst_add, Int.cast_add]

/-- Actual consecutiveness forces the omitted mediant above the cutoff;
the same height is the sum of the two actual endpoint heights. -/
theorem signedConsecutiveCutoffSlopes_height_bounds
    (k : Fin 8) (H : ℕ) (u v : ℤ × ℤ) (h : ConsecutiveCutoffSlopes H u v) :
    1 ≤ intHeight (inverseSignedSectorCoordinates k u) ∧
      intHeight (inverseSignedSectorCoordinates k u) ≤ (H : ℝ) ∧
      1 ≤ intHeight (inverseSignedSectorCoordinates k v) ∧
      intHeight (inverseSignedSectorCoordinates k v) ≤ (H : ℝ) ∧
      intHeight (inverseSignedSectorCoordinates k u + inverseSignedSectorCoordinates k v) =
        intHeight (inverseSignedSectorCoordinates k u) +
          intHeight (inverseSignedSectorCoordinates k v) ∧
      (H : ℝ) < intHeight (inverseSignedSectorCoordinates k u +
        inverseSignedSectorCoordinates k v) ∧
      (H : ℝ) < intHeight (inverseSignedSectorCoordinates k u) +
        intHeight (inverseSignedSectorCoordinates k v) ∧
      intHeight (inverseSignedSectorCoordinates k u) +
        intHeight (inverseSignedSectorCoordinates k v) ≤ 2 * (H : ℝ) ∧
      1 < intHeight (inverseSignedSectorCoordinates k u +
        inverseSignedSectorCoordinates k v) ∧
      1 < intHeight (inverseSignedSectorCoordinates k u) +
        intHeight (inverseSignedSectorCoordinates k v) := by
  obtain ⟨hu0, huH⟩ := inverseSignedSectorCoordinates_cutoff_height_bounds k H u h.1
  obtain ⟨hv0, hvH⟩ := inverseSignedSectorCoordinates_cutoff_height_bounds k H v h.2.1
  obtain ⟨_, huq, huqp, _, _⟩ := (mem_cutoffSlopesUpTo H u).mp h.1
  obtain ⟨_, hvq, hvqp, _, _⟩ := (mem_cutoffSlopesUpTo H v).mp h.2.1
  have hadd := inverseSignedSectorCoordinates_height_add_eq_of_canonical k u v
    huq huqp hvq hvqp
  have hsum : (H : ℝ) < intHeight (inverseSignedSectorCoordinates k u) +
      intHeight (inverseSignedSectorCoordinates k v) := by
    rw [inverseSignedSectorCoordinates_height_eq_first_of_cutoff k H u h.1,
      inverseSignedSectorCoordinates_height_eq_first_of_cutoff k H v h.2.1]
    exact_mod_cast (consecutiveCutoffSlopes_det_and_denominator_sum H u v h).2
  refine ⟨hu0, huH, hv0, hvH, hadd, ?_, hsum, ?_, ?_, ?_⟩
  · rwa [hadd]
  · linarith
  · rw [hadd]
    linarith
  · linarith

end Markov
