import Markov.SignedTraceArcs
import Markov.CutoffGapCoverage

/-! Real signed sectors cover the entire unit boundary outside the actual
primitive cutoff. All changes are changes of basis in the original normed
space; no reflection invariance of its norm is assumed. -/

noncomputable section
namespace Markov

/-- The eight signed coordinate sectors cover every real pair. -/
theorem exists_signedPairCoordinates_real (p : ℝ × ℝ) :
    ∃ k : Fin 8, 0 ≤ (signedPairCoordinates k p).2 ∧
      (signedPairCoordinates k p).2 ≤ (signedPairCoordinates k p).1 := by
  by_cases hp : 0 ≤ p.1
  · by_cases hq : 0 ≤ p.2
    · by_cases hqp : p.2 ≤ p.1
      · exact ⟨0, hq, hqp⟩
      · exact ⟨4, hp, le_of_lt (lt_of_not_ge hqp)⟩
    · by_cases hqp : -p.2 ≤ p.1
      · exact ⟨7, by dsimp [signedPairCoordinates]; linarith, hqp⟩
      · exact ⟨3, hp, le_of_lt (lt_of_not_ge hqp)⟩
  · by_cases hq : 0 ≤ p.2
    · by_cases hqp : p.2 ≤ -p.1
      · exact ⟨5, hq, hqp⟩
      · exact ⟨1, by dsimp [signedPairCoordinates]; linarith,
          le_of_lt (lt_of_not_ge hqp)⟩
    · by_cases hqp : -p.2 ≤ -p.1
      · exact ⟨2, by dsimp [signedPairCoordinates]; linarith, hqp⟩
      · exact ⟨6, by dsimp [signedPairCoordinates]; linarith,
          le_of_lt (lt_of_not_ge hqp)⟩

/-- A nonzero real pair has strictly positive first sector coordinate. -/
theorem exists_positive_signedPairCoordinates_real (p : ℝ × ℝ) (hp : p ≠ (0, 0)) :
    ∃ k : Fin 8, 0 < (signedPairCoordinates k p).1 ∧
      0 ≤ (signedPairCoordinates k p).2 ∧
      (signedPairCoordinates k p).2 ≤ (signedPairCoordinates k p).1 := by
  obtain ⟨k, hq, hqp⟩ := exists_signedPairCoordinates_real p
  refine ⟨k, ?_, hq, hqp⟩
  by_contra hn
  have hz : signedPairCoordinates k p = (0, 0) := by
    ext <;> dsimp <;> linarith
  have hzero : signedPairCoordinates (signedSectorInverse k) ((0, 0) : ℝ × ℝ) = (0, 0) := by
    fin_cases k <;> norm_num [signedSectorInverse, signedPairCoordinates]
  apply hp
  have he := congrArg (signedPairCoordinates (signedSectorInverse k)) hz
  simpa only [signedPairCoordinates_inverse, hzero] using he

/-- The coordinates in the signed basis are the actual signed permutation
of the coordinates in the original basis. -/
theorem signedSectorBasis_coord_pair {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : Module.Basis (Fin 2) ℝ E) (k : Fin 8) (x : E) :
    ((signedSectorBasis B k).coord 0 x, (signedSectorBasis B k).coord 1 x) =
      signedPairCoordinates k (B.coord 0 x, B.coord 1 x) := by
  fin_cases k <;> ext <;>
    simp [signedSectorBasis, Module.Basis.coord_apply, Module.Basis.map,
      sectorBasisEuclideanEquiv, signedEuclideanEquiv, signedSectorInverse,
      signedEuclideanCoordinates, signedPairCoordinates]

/-- Every nonzero real vector belongs to one of the actual signed bases'
closed canonical sectors. -/
theorem exists_signedSectorBasis_coords {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : Module.Basis (Fin 2) ℝ E) (x : E) (hx : x ≠ 0) :
    ∃ k : Fin 8, 0 < (signedSectorBasis B k).coord 0 x ∧
      0 ≤ (signedSectorBasis B k).coord 1 x ∧
      (signedSectorBasis B k).coord 1 x ≤ (signedSectorBasis B k).coord 0 x := by
  have hp : (B.coord 0 x, B.coord 1 x) ≠ (0, 0) := by
    intro h
    apply hx
    apply B.repr.injective
    ext i
    fin_cases i
    · simpa only [Module.Basis.coord_apply, map_zero, Finsupp.zero_apply] using
        congrArg (fun p : ℝ × ℝ => p.1) h
    · simpa only [Module.Basis.coord_apply, map_zero, Finsupp.zero_apply] using
        congrArg (fun p : ℝ × ℝ => p.2) h
  obtain ⟨k, hk0, hk1, hk10⟩ :=
    exists_positive_signedPairCoordinates_real (B.coord 0 x, B.coord 1 x) hp
  have he := signedSectorBasis_coord_pair B k x
  have h0 := congrArg Prod.fst he
  have h1 := congrArg Prod.snd he
  exact ⟨k, by simpa only [← h0] using hk0,
    by simpa only [← h1] using hk1, by simpa only [← h0, ← h1] using hk10⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every positive cutoff contains the canonical sector's two endpoint
directions on the actual norm boundary. -/
theorem radialBasisSection_endpoints_mem_cutoffCorners
    (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) (hH : 1 ≤ H) :
    radialBasisSection B 0 ∈ cutoffCorners B H ∧
      radialBasisSection B 1 ∈ cutoffCorners B H := by
  have hend := cutoffSlopesUpTo_endpoints_mem H hH
  constructor
  · have hm := normalize_mem_cutoffCorners B H (1, 0) hend.1
    rw [normalize_intVector_eq_radialBasisSection B (1, 0) (by norm_num)] at hm
    simpa only [cutoffSlope, Int.cast_one, Int.cast_zero, zero_div] using hm
  · have hm := normalize_mem_cutoffCorners B H (1, 1) hend.2
    rw [normalize_intVector_eq_radialBasisSection B (1, 1) (by norm_num)] at hm
    simpa only [cutoffSlope, Int.cast_one, one_div_one] using hm

/-- A unit point outside the primitive cutoff lies strictly inside one
signed sector, because all sector endpoints occur in every positive cutoff. -/
theorem exists_signedSectorBasis_strict_slope_of_uncut
    (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) (hH : 1 ≤ H)
    (x : E) (hx : ‖x‖ = 1) (hxNotCut : x ∉ cutoffCorners B H) :
    ∃ k : Fin 8, 0 < (signedSectorBasis B k).coord 0 x ∧
      basisSlope (signedSectorBasis B k) x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hx0 : x ≠ 0 := by
    intro hz
    simp only [hz, norm_zero] at hx
    norm_num at hx
  obtain ⟨k, hk0, hk1, hk10⟩ := exists_signedSectorBasis_coords B x hx0
  have hs0 : 0 ≤ basisSlope (signedSectorBasis B k) x := div_nonneg hk1 hk0.le
  have hs1 : basisSlope (signedSectorBasis B k) x ≤ 1 := (div_le_one hk0).mpr hk10
  have he := radialBasisSection_basisSlope (signedSectorBasis B k) x hx hk0
  have hend := radialBasisSection_endpoints_mem_cutoffCorners (signedSectorBasis B k) H hH
  have hne0 : basisSlope (signedSectorBasis B k) x ≠ 0 := by
    intro hs
    rw [hs] at he
    apply hxNotCut
    rw [← cutoffCorners_signedSectorBasis B k H, ← he]
    exact hend.1
  have hne1 : basisSlope (signedSectorBasis B k) x ≠ 1 := by
    intro hs
    rw [hs] at he
    apply hxNotCut
    rw [← cutoffCorners_signedSectorBasis B k H, ← he]
    exact hend.2
  exact ⟨k, hk0, lt_of_le_of_ne hs0 (Ne.symm hne0), lt_of_le_of_ne hs1 hne1⟩

/-- The strict sector coverage also supplies the actual radial
parametrization of the original unit point. -/
theorem exists_signedSectorBasis_radial_of_uncut
    (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) (hH : 1 ≤ H)
    (x : E) (hx : ‖x‖ = 1) (hxNotCut : x ∉ cutoffCorners B H) :
    ∃ k : Fin 8, ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      radialBasisSection (signedSectorBasis B k) t = x := by
  obtain ⟨k, hk0, hkt⟩ := exists_signedSectorBasis_strict_slope_of_uncut B H hH x hx hxNotCut
  exact ⟨k, basisSlope (signedSectorBasis B k) x, hkt,
    radialBasisSection_basisSlope (signedSectorBasis B k) x hx hk0⟩

end Markov
