import Markov.CutoffArcs
import Markov.BoundaryNormals

/-! Positive combinations of two ordered rays stay in their actual open
boundary arc. This supplies the local-wedge inclusion at a cutoff endpoint,
without assuming the selected normal already belongs to that arc's closure. -/

noncomputable section
namespace Markov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalize_basis_combination (B : Module.Basis (Fin 2) ℝ E)
    (p q : ℝ) (hp : 0 < p) :
    NormedSpace.normalize (p • B 0 + q • B 1) = radialBasisSection B (q / p) := by
  have he : p • B 0 + q • B 1 = p • (B 0 + (q / p) • B 1) := by
    rw [smul_add, smul_smul]
    congr 1
    congr 1
    field_simp
  rw [he, NormedSpace.normalize_smul_of_pos hp]
  rfl

theorem radial_intPairBasis_mem_slopeBoundaryArc
    (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ) (hd : intDet u v ≠ 0)
    (hu : 0 < u.1) (hv : 0 < v.1) (horder : 0 < intDet u v)
    (t : ℝ) (ht : 0 < t) :
    radialBasisSection (intPairBasis B u v hd) t ∈
      slopeBoundaryArc B (cutoffSlope u) (cutoffSlope v) := by
  have hup : (0 : ℝ) < u.1 := by exact_mod_cast hu
  have hvp : (0 : ℝ) < v.1 := by exact_mod_cast hv
  have hdet : 0 < (u.1 : ℝ) * v.2 - (u.2 : ℝ) * v.1 := by exact_mod_cast horder
  have hp : 0 < (u.1 : ℝ) + t * v.1 := by positivity
  have he : radialBasisSection (intPairBasis B u v hd) t =
      radialBasisSection B (((u.2 : ℝ) + t * v.2) / ((u.1 : ℝ) + t * v.1)) := by
    simp only [radialBasisSection, intPairBasis_zero, intPairBasis_one]
    rw [show intVector B u + t • intVector B v =
      ((u.1 : ℝ) + t * v.1) • B 0 + ((u.2 : ℝ) + t * v.2) • B 1 by
        dsimp [intVector]; module]
    exact normalize_basis_combination B _ _ hp
  rw [he]
  refine ⟨norm_radialBasisSection B _, radialBasisSection_coord_zero_pos B _, ?_, ?_⟩
  · rw [basisSlope_radialBasisSection]
    apply (div_lt_div_iff₀ hup hp).mpr
    nlinarith [mul_pos ht hdet]
  · rw [basisSlope_radialBasisSection]
    apply (div_lt_div_iff₀ hp hvp).mpr
    nlinarith

theorem intPairBasis_local_arc_subset_slopeBoundaryArc
    (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ) (hd : intDet u v ≠ 0)
    (hu : 0 < u.1) (hv : 0 < v.1) (horder : 0 < intDet u v) (ε : ℝ) :
    slopeBoundaryArc (intPairBasis B u v hd) 0 ε ⊆
      slopeBoundaryArc B (cutoffSlope u) (cutoffSlope v) := by
  rw [← radialBasisSection_image_Ioo]
  rintro x ⟨t, ht, rfl⟩
  exact radial_intPairBasis_mem_slopeBoundaryArc B u v hd hu hv horder t ht.1

/-- The local endpoint-normal closure lies in the normal closure of the
entire actual consecutive cutoff arc. -/
theorem consecutiveCutoffSlopes_selectedSupport_normal_mem_closure
    (B C : Module.Basis (Fin 2) ℝ E) (H : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H u v) :
    normalizedEuclideanCovector C (selectedSupportAt B u v) ∈
      closure (normalsOn C (slopeBoundaryArc B (cutoffSlope u) (cutoffSlope v))) := by
  have hdet : intDet u v = 1 := (consecutiveCutoffSlopes_det_and_denominator_sum H u v h).1
  have hd : intDet u v ≠ 0 := by omega
  have hlocal := selectedSupportAt_normal_mem_closure_normalsOn_slopeBoundaryArc
    B C u v hd 1 (by norm_num)
  apply (closure_mono (normalsOn_mono C
    (intPairBasis_local_arc_subset_slopeBoundaryArc B u v hd
      ((mem_cutoffSlopesUpTo H u).mp h.1).1
      ((mem_cutoffSlopesUpTo H v).mp h.2.1).1 (by omega) 1))) hlocal

end Markov
