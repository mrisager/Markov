import Markov.SupportShear
import Markov.ChordHalfPlane

/-! Selected supporting functionals are invariant under positive rescaling of
the norming ray and positive rescaling and shear of the selecting direction.
These statements allow the same actual support to be identified in any
adapted real basis. -/

noncomputable section

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive rescaling of the norming ray preserves selected supports. -/
theorem isSelectedSupport_pos_smul_left_iff (a b : E) (c : ℝ) (hc : 0 < c)
    (f : StrongDual ℝ E) :
    IsSelectedSupport (c • a) b f ↔ IsSelectedSupport a b f := by
  simp only [IsSelectedSupport, normingFunctionals_pos_smul_eq a c hc]

/-- Positive rescaling of the direction being maximized preserves selected
supports. -/
theorem isSelectedSupport_pos_smul_right_iff (a b : E) (d : ℝ) (hd : 0 < d)
    (f : StrongDual ℝ E) :
    IsSelectedSupport a (d • b) f ↔ IsSelectedSupport a b f := by
  constructor
  · rintro ⟨hf, hmax⟩
    refine ⟨hf, ?_⟩
    intro g hg
    have h := hmax g hg
    simp only [map_smul, smul_eq_mul] at h
    exact le_of_mul_le_mul_left h hd
  · rintro ⟨hf, hmax⟩
    refine ⟨hf, ?_⟩
    intro g hg
    simpa only [map_smul, smul_eq_mul] using
      mul_le_mul_of_nonneg_left (hmax g hg) hd.le

/-- Transport along a positive norming-ray scaling and an oriented shear
and scaling of the second direction. -/
theorem isSelectedSupport_pos_smul_shear_iff (a b : E) (c d s : ℝ)
    (hc : 0 < c) (hd : 0 < d) (f : StrongDual ℝ E) :
    IsSelectedSupport (c • a) (d • b + s • a) f ↔ IsSelectedSupport a b f := by
  rw [isSelectedSupport_pos_smul_left_iff a _ c hc,
    isSelectedSupport_shear_iff a (d • b) s,
    isSelectedSupport_pos_smul_right_iff a b d hd]

/-- An adapted real basis gives uniqueness for the selected support of its
two prescribed vectors. -/
theorem isSelectedSupport_unique_of_basis (B : Module.Basis (Fin 2) ℝ E)
    (a b : E) (ha : B 0 = a) (hb : B 1 = b) (f g : StrongDual ℝ E)
    (hf : IsSelectedSupport a b f) (hg : IsSelectedSupport a b g) : f = g := by
  apply (exists_unique_selectedSupport B).unique
  · simpa only [ha, hb] using hf
  · simpa only [ha, hb] using hg

/-- Selection in any adapted basis is characterized by equality to the
constructed selected support. -/
theorem isSelectedSupport_iff_eq_selectedSupport_of_basis
    (B : Module.Basis (Fin 2) ℝ E) (a b : E) (ha : B 0 = a) (hb : B 1 = b)
    (f : StrongDual ℝ E) :
    IsSelectedSupport a b f ↔ f = selectedSupport B := by
  constructor
  · intro hf
    exact isSelectedSupport_unique_of_basis B a b ha hb f (selectedSupport B) hf
      (by simpa only [ha, hb] using selectedSupport_spec B)
  · intro hf
    simpa only [hf, ha, hb] using selectedSupport_spec B

/-- A selected support is independent of an adapted basis chosen along the
same norming ray and on the same side of that ray. -/
theorem selectedSupport_eq_of_pos_smul_shear
    (B C : Module.Basis (Fin 2) ℝ E) (c d s : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hzero : C 0 = c • B 0) (hone : C 1 = d • B 1 + s • B 0) :
    selectedSupport C = selectedSupport B := by
  apply (exists_unique_selectedSupport B).unique
  · have hC := selectedSupport_spec C
    rw [hzero, hone, isSelectedSupport_pos_smul_shear_iff (B 0) (B 1) c d s hc hd]
      at hC
    exact hC
  · exact selectedSupport_spec B

end Markov
