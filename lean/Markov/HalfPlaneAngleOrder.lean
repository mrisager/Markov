import Markov.SupportAngleEnvelope
import Markov.SupportNormalOrder
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! On the open half-plane `re + im > 0`, the principal complex argument
is ordered by the determinant. This supplies an actual angular order for
supporting normals from the order already proved by their support inequalities. -/

noncomputable section

namespace Markov

theorem complex_arg_eq_arctan_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) := by
  have hb := (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  have ht := Complex.tan_arg z
  exact (Real.arctan_eq_of_tan_eq ht (abs_lt.mp hb)).symm

/-- The principal argument has a single explicit branch on this half-plane. -/
theorem complex_arg_eq_arctan_of_sum_pos (z : ℂ) (hz : 0 < z.re + z.im) :
    z.arg = Real.arctan ((z.im - z.re) / (z.re + z.im)) + Real.pi / 4 := by
  let v : ℂ := ⟨z.re + z.im, z.im - z.re⟩
  let k : ℂ := ⟨1, 1⟩
  have hv : 0 < v.re := hz
  have hv0 : v ≠ 0 := by
    intro h
    simp [h] at hv
  have hk0 : k ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num [k] at this
  have hka : k.arg = Real.pi / 4 := by
    rw [complex_arg_eq_arctan_of_re_pos k (by norm_num [k])]
    simp [k, Real.arctan_one]
  have hva : v.arg = Real.arctan ((z.im - z.re) / (z.re + z.im)) :=
    complex_arg_eq_arctan_of_re_pos v hv
  have hbounds := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hv))
  have hmul : (k * v).arg = k.arg + v.arg := by
    apply Complex.arg_mul hk0 hv0
    rw [hka]
    constructor <;> linarith [Real.pi_pos]
  have hprod : k * v = (2 : ℝ) * z := by
    apply Complex.ext <;> simp [k, v, Complex.mul_re, Complex.mul_im] <;> ring
  rw [hprod, Complex.arg_real_mul z (by norm_num), hka, hva] at hmul
  linarith only [hmul]

/-- Within the positive-sum half-plane, determinant order is exactly angle order. -/
theorem complex_arg_le_iff_det_nonneg_of_sum_pos (z w : ℂ)
    (hz : 0 < z.re + z.im) (hw : 0 < w.re + w.im) :
    z.arg ≤ w.arg ↔ 0 ≤ z.re * w.im - z.im * w.re := by
  rw [complex_arg_eq_arctan_of_sum_pos z hz, complex_arg_eq_arctan_of_sum_pos w hw,
    add_le_add_iff_right, Real.arctan_le_arctan_iff, div_le_div_iff₀ hz hw]
  constructor <;> intro h <;> nlinarith only [h]

theorem complex_arg_le_of_sum_pos_of_det_nonneg (z w : ℂ)
    (hz : 0 < z.re + z.im) (hw : 0 < w.re + w.im)
    (hdet : 0 ≤ z.re * w.im - z.im * w.re) : z.arg ≤ w.arg :=
  (complex_arg_le_iff_det_nonneg_of_sum_pos z w hz hw).mpr hdet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem supportAngle_le_iff_det_nonneg_of_sum_pos
    (B : Module.Basis (Fin 2) ℝ E) (f g : StrongDual ℝ E)
    (hf : 0 < f (B 0) + f (B 1)) (hg : 0 < g (B 0) + g (B 1)) :
    supportAngle B f ≤ supportAngle B g ↔
      0 ≤ f (B 0) * g (B 1) - f (B 1) * g (B 0) :=
  complex_arg_le_iff_det_nonneg_of_sum_pos (supportComplex B f) (supportComplex B g) hf hg

/-- The actual supports increase in angle when their parameter increases
and both supports belong to the positive-sum half-plane. -/
theorem normingSupport_basisLine_supportAngle_le
    (B : Module.Basis (Fin 2) ℝ E) (s t : ℝ) (hst : s < t)
    (fs ft : StrongDual ℝ E)
    (hfs : fs ∈ normingFunctionals (B 0 + s • B 1))
    (hft : ft ∈ normingFunctionals (B 0 + t • B 1))
    (hfspos : 0 < fs (B 0) + fs (B 1))
    (hftpos : 0 < ft (B 0) + ft (B 1)) :
    supportAngle B fs ≤ supportAngle B ft := by
  apply (supportAngle_le_iff_det_nonneg_of_sum_pos B fs ft hfspos hftpos).mpr
  exact normingSupport_affineLine_det_nonneg (B 0) (B 1) s t hst fs ft hfs hft

/-- Any actual support selection in this common half-plane gives a monotone
real angle, including selections that jump at nonsmooth boundary points. -/
theorem normingSupport_basisLine_supportAngle_monotoneOn
    (B : Module.Basis (Fin 2) ℝ E) (S : Set ℝ) (f : ℝ → StrongDual ℝ E)
    (hf : ∀ t ∈ S, f t ∈ normingFunctionals (B 0 + t • B 1))
    (hfpos : ∀ t ∈ S, 0 < f t (B 0) + f t (B 1)) :
    MonotoneOn (fun t => supportAngle B (f t)) S := by
  intro s hs t ht hst
  rcases eq_or_lt_of_le hst with rfl | hst
  · exact le_rfl
  · exact normingSupport_basisLine_supportAngle_le B s t hst (f s) (f t)
      (hf s hs) (hf t ht) (hfpos s hs) (hfpos t ht)

/-- At a fixed parameter the angle orders the support fibre by its second
evaluation, with no assumed angular ordering. -/
theorem normingSupport_basisLine_sameParameter_supportAngle_le_iff
    (B : Module.Basis (Fin 2) ℝ E) (t : ℝ) (f g : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals (B 0 + t • B 1))
    (hg : g ∈ normingFunctionals (B 0 + t • B 1))
    (hfpos : 0 < f (B 0) + f (B 1))
    (hgpos : 0 < g (B 0) + g (B 1)) :
    supportAngle B f ≤ supportAngle B g ↔ f (B 1) ≤ g (B 1) := by
  rw [supportAngle_le_iff_det_nonneg_of_sum_pos B f g hfpos hgpos]
  exact normingSupport_basisLine_sameParameter_det_nonneg_iff B t f g hf hg

end Markov
