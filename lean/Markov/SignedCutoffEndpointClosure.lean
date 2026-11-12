import Markov.BoundaryWedgeInclusion
import Markov.SignedSelectedSupport
import Markov.SignedCutoffTurnDecay

/-! Both inward selected endpoint normals belong to the closure of the
actual normals on each signed cutoff component. The right endpoint is
approached through the reversed local cone. All vectors and supports stay
in the original normed space, so no reflection symmetry is needed. -/

noncomputable section
open Set

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Reversing the endpoint basis parametrizes the same positive cone,
with reciprocal positive parameter. -/
theorem radial_intPairBasis_reverse_mem_slopeBoundaryArc
    (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ)
    (hd : intDet u v ≠ 0) (hdr : intDet v u ≠ 0)
    (hu : 0 < u.1) (hv : 0 < v.1) (horder : 0 < intDet u v)
    (t : ℝ) (ht : 0 < t) :
    radialBasisSection (intPairBasis B v u hdr) t ∈
      slopeBoundaryArc B (cutoffSlope u) (cutoffSlope v) := by
  have he : intVector B v + t • intVector B u =
      t • (intVector B u + t⁻¹ • intVector B v) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    exact add_comm _ _
  have hsection : radialBasisSection (intPairBasis B v u hdr) t =
      radialBasisSection (intPairBasis B u v hd) t⁻¹ := by
    simp only [radialBasisSection, intPairBasis_zero, intPairBasis_one]
    rw [he, NormedSpace.normalize_smul_of_pos ht]
  rw [hsection]
  exact radial_intPairBasis_mem_slopeBoundaryArc B u v hd hu hv horder
    t⁻¹ (inv_pos.mpr ht)

/-- The local arc beginning at the right endpoint enters the same open
slope component as the local arc beginning at the left endpoint. -/
theorem intPairBasis_reverse_local_arc_subset_slopeBoundaryArc
    (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ)
    (hd : intDet u v ≠ 0) (hdr : intDet v u ≠ 0)
    (hu : 0 < u.1) (hv : 0 < v.1) (horder : 0 < intDet u v) (ε : ℝ) :
    slopeBoundaryArc (intPairBasis B v u hdr) 0 ε ⊆
      slopeBoundaryArc B (cutoffSlope u) (cutoffSlope v) := by
  rw [← radialBasisSection_image_Ioo]
  rintro x ⟨t, ht, rfl⟩
  exact radial_intPairBasis_reverse_mem_slopeBoundaryArc
    B u v hd hdr hu hv horder t ht.1

/-- The incoming selected normal at the right endpoint is approached by
genuine normals on the actual consecutive cutoff arc. -/
theorem consecutiveCutoffSlopes_reverse_selectedSupport_normal_mem_closure
    (B C : Module.Basis (Fin 2) ℝ E) (H : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H u v) :
    normalizedEuclideanCovector C (selectedSupportAt B v u) ∈
      closure (normalsOn C (slopeBoundaryArc B (cutoffSlope u) (cutoffSlope v))) := by
  have hdet : intDet u v = 1 :=
    (consecutiveCutoffSlopes_det_and_denominator_sum H u v h).1
  have hd : intDet u v ≠ 0 := by omega
  have hdr : intDet v u ≠ 0 := by
    have hreversed : intDet v u = -intDet u v := by
      dsimp [intDet]
      ring
    rw [hreversed, hdet]
    norm_num
  have hlocal := selectedSupportAt_normal_mem_closure_normalsOn_slopeBoundaryArc
    B C v u hdr 1 (by norm_num)
  apply (closure_mono (normalsOn_mono C
    (intPairBasis_reverse_local_arc_subset_slopeBoundaryArc B u v hd hdr
      ((mem_cutoffSlopesUpTo H u).mp h.1).1
      ((mem_cutoffSlopesUpTo H v).mp h.2.1).1 (by omega) 1))) hlocal

/-- The original actual left selected support is the selected support in
the signed basis, with the inverse signed integer coordinates. -/
theorem signedConsecutiveCutoffSlopes_selectedSupport_normal_mem_closure
    (B C : Module.Basis (Fin 2) ℝ E) (H : ℕ) (k : Fin 8) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H u v) :
    normalizedEuclideanCovector C
      (selectedSupportAt B (inverseSignedSectorCoordinates k u)
        (inverseSignedSectorCoordinates k v)) ∈
      closure (normalsOn C
        (slopeBoundaryArc (signedSectorBasis B k) (cutoffSlope u) (cutoffSlope v))) := by
  have he := selectedSupportAt_signedSectorBasis B k
    (inverseSignedSectorCoordinates k u) (inverseSignedSectorCoordinates k v)
  simp only [coordinates_inverseSignedSectorCoordinates] at he
  rw [← he]
  exact consecutiveCutoffSlopes_selectedSupport_normal_mem_closure
    (signedSectorBasis B k) C H u v h

/-- The original actual incoming right selected support is approached
inside the signed component, including in orientation reversing sectors. -/
theorem signedConsecutiveCutoffSlopes_reverse_selectedSupport_normal_mem_closure
    (B C : Module.Basis (Fin 2) ℝ E) (H : ℕ) (k : Fin 8) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H u v) :
    normalizedEuclideanCovector C
      (selectedSupportAt B (inverseSignedSectorCoordinates k v)
        (inverseSignedSectorCoordinates k u)) ∈
      closure (normalsOn C
        (slopeBoundaryArc (signedSectorBasis B k) (cutoffSlope u) (cutoffSlope v))) := by
  have he := selectedSupportAt_signedSectorBasis B k
    (inverseSignedSectorCoordinates k v) (inverseSignedSectorCoordinates k u)
  simp only [coordinates_inverseSignedSectorCoordinates] at he
  rw [← he]
  exact consecutiveCutoffSlopes_reverse_selectedSupport_normal_mem_closure
    (signedSectorBasis B k) C H u v h

/-- Both original endpoint normals lie in the closure of the genuine
normal set of the actual signed trace cutoff component. -/
theorem signedConsecutiveCutoffSlopes_both_selectedSupport_normals_mem_closure
    (H : ℕ) (k : Fin 8) (u v : ℤ × ℤ) (h : ConsecutiveCutoffSlopes H u v) :
    normalizedEuclideanCovector traceBasis
      (selectedSupportAt traceBasis (inverseSignedSectorCoordinates k u)
        (inverseSignedSectorCoordinates k v)) ∈
      closure (normalsOn traceBasis
        (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))) ∧
    normalizedEuclideanCovector traceBasis
      (selectedSupportAt traceBasis (inverseSignedSectorCoordinates k v)
        (inverseSignedSectorCoordinates k u)) ∈
      closure (normalsOn traceBasis
        (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))) :=
  ⟨signedConsecutiveCutoffSlopes_selectedSupport_normal_mem_closure
      traceBasis traceBasis H k u v h,
    signedConsecutiveCutoffSlopes_reverse_selectedSupport_normal_mem_closure
      traceBasis traceBasis H k u v h⟩

end Markov
