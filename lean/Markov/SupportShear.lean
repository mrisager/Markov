import Markov.FareyHolonomy
import Markov.UnimodularPartners

/-! Selection of a supporting functional depends on the side of the
second direction, not its integral shear by the first direction. -/

noncomputable section

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Adding a multiple of the norming direction adds the same scalar to every
candidate functional, so the selected maximizers remain the same. -/
theorem isSelectedSupport_shear_iff (a b : E) (s : ℝ) (f : StrongDual ℝ E) :
    IsSelectedSupport a (b + s • a) f ↔ IsSelectedSupport a b f := by
  constructor
  · rintro ⟨hf, hmax⟩
    refine ⟨hf, ?_⟩
    intro g hg
    have h := hmax g hg
    simp only [map_add, map_smul, hf.2, hg.2, smul_eq_mul] at h
    linarith
  · rintro ⟨hf, hmax⟩
    refine ⟨hf, ?_⟩
    intro g hg
    have h := hmax g hg
    simp only [map_add, map_smul, hf.2, hg.2, smul_eq_mul]
    linarith

theorem intVector_zsmul_add (B : Module.Basis (Fin 2) ℝ E)
    (u v : ℤ × ℤ) (k : ℤ) :
    intVector B (v + k • u) = intVector B v + (k : ℝ) • intVector B u := by
  simp [intVector, zsmul_eq_mul, smul_add, add_smul, smul_smul]
  module

theorem intDet_shear (u v : ℤ × ℤ) (k : ℤ) : intDet u (v + k • u) = intDet u v := by
  simp [intDet, zsmul_eq_mul]
  ring

/-- The actual constructed selected functional is invariant under shear. -/
theorem selectedSupportAt_shear (B : Module.Basis (Fin 2) ℝ E)
    (u v : ℤ × ℤ) (k : ℤ) (hdet : intDet u v ≠ 0) :
    selectedSupportAt B u (v + k • u) = selectedSupportAt B u v := by
  have hd : intDet u (v + k • u) ≠ 0 := by rwa [intDet_shear]
  have hs := selectedSupportAt_spec B u (v + k • u) hd
  rw [intVector_zsmul_add, isSelectedSupport_shear_iff] at hs
  have ht := selectedSupportAt_spec B u v hdet
  exact (exists_unique_selectedSupport (intPairBasis B u v hdet)).unique
    (by simpa only [intPairBasis_zero, intPairBasis_one] using hs)
    (by simpa only [intPairBasis_zero, intPairBasis_one] using ht)

/-- Any two integral partners on the same unimodular side select the same
support. This permits replacement by a bounded Farey partner. -/
theorem selectedSupportAt_eq_of_unimodular (B : Module.Basis (Fin 2) ℝ E)
    (u v w : ℤ × ℤ) (hv : intDet u v = 1) (hw : intDet u w = 1) :
    selectedSupportAt B u v = selectedSupportAt B u w := by
  rw [unimodular_partners_shear u v w hv hw]
  exact selectedSupportAt_shear B u w _ (by omega)

theorem selectedSupportAt_eq_of_neg_unimodular (B : Module.Basis (Fin 2) ℝ E)
    (u v w : ℤ × ℤ) (hv : intDet u v = -1) (hw : intDet u w = -1) :
    selectedSupportAt B u v = selectedSupportAt B u w := by
  rw [neg_unimodular_partners_shear u v w hv hw]
  exact selectedSupportAt_shear B u w _ (by omega)

end Markov
