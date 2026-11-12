import Markov.SignedSectors

/-! Selected supports commute with signed changes of integer coordinates when
the basis is changed in the opposite direction. Both norming and selecting
vectors are exactly the original vectors in the original normed space; no
reflection invariance of the norm is used. -/

noncomputable section

namespace Markov

theorem signedSectorCoordinates_det_ne_zero_iff (k : Fin 8) (u v : ℤ × ℤ) :
    intDet (signedSectorCoordinates k u) (signedSectorCoordinates k v) ≠ 0 ↔
      intDet u v ≠ 0 := by
  constructor
  · intro h hzero
    apply h
    apply abs_eq_zero.mp
    rw [signedSectorCoordinates_abs_det, hzero, abs_zero]
  · intro h hzero
    apply h
    apply abs_eq_zero.mp
    rw [← signedSectorCoordinates_abs_det k u v, hzero, abs_zero]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Changing the integer coordinates and the basis in opposite directions
leaves the actual selected functional unchanged, including the zero fallback
for dependent integer vectors. -/
theorem selectedSupportAt_signedSectorBasis (B : Module.Basis (Fin 2) ℝ E)
    (k : Fin 8) (u v : ℤ × ℤ) :
    selectedSupportAt (signedSectorBasis B k)
      (signedSectorCoordinates k u) (signedSectorCoordinates k v) =
      selectedSupportAt B u v := by
  by_cases hdet : intDet u v ≠ 0
  · have hdet' := (signedSectorCoordinates_det_ne_zero_iff k u v).mpr hdet
    have hs := selectedSupportAt_spec (signedSectorBasis B k)
      (signedSectorCoordinates k u) (signedSectorCoordinates k v) hdet'
    rw [signedSectorBasis_intVector, signedSectorBasis_intVector] at hs
    have ht := selectedSupportAt_spec B u v hdet
    apply (exists_unique_selectedSupport (intPairBasis B u v hdet)).unique
    · simpa only [intPairBasis_zero, intPairBasis_one] using hs
    · simpa only [intPairBasis_zero, intPairBasis_one] using ht
  · have hdet' : ¬intDet (signedSectorCoordinates k u) (signedSectorCoordinates k v) ≠ 0 :=
      fun h => hdet ((signedSectorCoordinates_det_ne_zero_iff k u v).mp h)
    simp only [selectedSupportAt, dif_neg hdet, dif_neg hdet']

end Markov
