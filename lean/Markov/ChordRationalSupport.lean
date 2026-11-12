import Markov.SelectedSupportTransport
import Markov.ChordCornerGeometry
import Markov.FareyProfile

/-! The actual supports at a determinant-one integer pair are the outgoing
and incoming supports of the corresponding rational chord parameters.
Only positivity of the relevant coordinate sum is needed; coordinate signs
and symmetries of the norm play no role in the identification. -/

noncomputable section

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An integer vector is a positive radial multiple of its rational chord
point when its coordinate sum is positive. -/
theorem intVector_eq_profileMass_smul_chordPoint
    (B : Module.Basis (Fin 2) ℝ E) (u : ℤ × ℤ) (hu : profileMass u ≠ 0) :
    intVector B u = profileMass u •
      ((1 - profileParameter u) • B 0 + profileParameter u • B 1) := by
  have hzero : profileMass u * (1 - profileParameter u) = (u.1 : ℝ) := by
    dsimp [profileParameter]
    field_simp [hu]
    dsimp [profileMass]
    ring
  have hone : profileMass u * profileParameter u = (u.2 : ℝ) := by
    dsimp [profileParameter]
    field_simp [hu]
  rw [smul_add, smul_smul, smul_smul, hzero, hone]
  rfl

/-- A determinant-one partner lies on the increasing side of the rational
chord point. -/
theorem intVector_eq_chordPoint_pos_shear_of_det_one
    (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ)
    (hu : profileMass u ≠ 0) (hdet : intDet u v = 1) :
    intVector B v = (profileMass u)⁻¹ • (B 1 - B 0) + profileMass v •
      ((1 - profileParameter u) • B 0 + profileParameter u • B 1) := by
  have hd : (u.1 : ℝ) * (v.2 : ℝ) - (u.2 : ℝ) * (v.1 : ℝ) = 1 := by
    exact_mod_cast hdet
  have hzero : -(profileMass u)⁻¹ +
      profileMass v * (1 - profileParameter u) = (v.1 : ℝ) := by
    dsimp [profileParameter]
    field_simp [hu]
    dsimp [profileMass]
    nlinarith only [hd]
  have hone : (profileMass u)⁻¹ + profileMass v * profileParameter u = (v.2 : ℝ) := by
    dsimp [profileParameter]
    field_simp [hu]
    dsimp [profileMass]
    nlinarith only [hd]
  simp only [intVector, smul_sub, smul_add, smul_smul]
  rw [← hzero, ← hone]
  module

/-- The first vector lies on the decreasing side of the second rational
chord point. -/
theorem intVector_eq_chordPoint_neg_shear_of_det_one
    (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ)
    (hv : profileMass v ≠ 0) (hdet : intDet u v = 1) :
    intVector B u = (profileMass v)⁻¹ • (-(B 1 - B 0)) + profileMass u •
      ((1 - profileParameter v) • B 0 + profileParameter v • B 1) := by
  have hd : (u.1 : ℝ) * (v.2 : ℝ) - (u.2 : ℝ) * (v.1 : ℝ) = 1 := by
    exact_mod_cast hdet
  have hzero : (profileMass v)⁻¹ +
      profileMass u * (1 - profileParameter v) = (u.1 : ℝ) := by
    dsimp [profileParameter]
    field_simp [hv]
    dsimp [profileMass]
    nlinarith only [hd]
  have hone : -(profileMass v)⁻¹ + profileMass u * profileParameter v = (u.2 : ℝ) := by
    dsimp [profileParameter]
    field_simp [hv]
    dsimp [profileMass]
    nlinarith only [hd]
  simp only [intVector, smul_neg, smul_sub, smul_add, smul_smul]
  rw [← hzero, ← hone]
  module

/-- The incoming chord support maximizes the negative chord direction. -/
theorem chordLeftSelectedSupport_spec (B : Module.Basis (Fin 2) ℝ E) (s : ℝ) :
    IsSelectedSupport ((1 - s) • B 0 + s • B 1) (-(B 1 - B 0))
      (chordLeftSelectedSupport B s) := by
  have h := leftSelectedAffineSupport_spec (chordBasis B) s
  rw [chordBasis_affinePoint, chordBasis_one] at h
  exact h

/-- At the first endpoint of a determinant-one pair, the actual arithmetic
selected support equals the outgoing rational chord support. -/
theorem selectedSupportAt_eq_chordSelectedSupport
    (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ)
    (hu : 0 < profileMass u) (hdet : intDet u v = 1) :
    selectedSupportAt B u v = chordSelectedSupport B (profileParameter u) := by
  have hs := selectedSupportAt_spec B u v (by omega)
  rw [intVector_eq_chordPoint_pos_shear_of_det_one B u v hu.ne' hdet,
    intVector_eq_profileMass_smul_chordPoint B u hu.ne',
    isSelectedSupport_pos_smul_shear_iff _ _ _ _ _ hu (inv_pos.mpr hu)] at hs
  apply isSelectedSupport_unique_of_basis
    (affinePairBasis (chordBasis B) (profileParameter u)) _ _ _ _ _ _ hs
    (chordSelectedSupport_spec B (profileParameter u))
  · rw [affinePairBasis_zero, chordBasis_affinePoint]
  · rw [affinePairBasis_one, chordBasis_one]

/-- At the second endpoint of a determinant-one pair, reversing the
arithmetic pair gives the incoming rational chord support. -/
theorem selectedSupportAt_rev_eq_chordLeftSelectedSupport
    (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ)
    (hv : 0 < profileMass v) (hdet : intDet u v = 1) :
    selectedSupportAt B v u = chordLeftSelectedSupport B (profileParameter v) := by
  have hrev : intDet v u ≠ 0 := by
    dsimp [intDet] at hdet ⊢
    nlinarith only [hdet]
  have hs := selectedSupportAt_spec B v u hrev
  rw [intVector_eq_chordPoint_neg_shear_of_det_one B u v hv.ne' hdet,
    intVector_eq_profileMass_smul_chordPoint B v hv.ne',
    isSelectedSupport_pos_smul_shear_iff _ _ _ _ _ hv (inv_pos.mpr hv)] at hs
  apply isSelectedSupport_unique_of_basis
    (reverseSecondBasis (affinePairBasis (chordBasis B) (profileParameter v)))
    _ _ _ _ _ _ hs (chordLeftSelectedSupport_spec B (profileParameter v))
  · rw [reverseSecondBasis_zero, affinePairBasis_zero, chordBasis_affinePoint]
  · rw [reverseSecondBasis_one, affinePairBasis_one, chordBasis_one]

end Markov
