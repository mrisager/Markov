import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! Metric translation length on the actual hyperbolic upper half-plane.
The length is an infimum of displacements, not a trace-based definition. -/

noncomputable section
open Set
open scoped MatrixGroups
namespace Markov

/-- The actual metric translation length of a real determinant-one matrix. -/
def hyperbolicTranslationLength (g : SL(2, ℝ)) : ℝ :=
  sInf (Set.range (fun z : UpperHalfPlane => dist z (g • z)))

private theorem hyperbolic_displacements_bddBelow (g : SL(2, ℝ)) :
    BddBelow (Set.range (fun z : UpperHalfPlane => dist z (g • z))) :=
  ⟨0, fun _ ⟨_, hz⟩ => hz ▸ dist_nonneg⟩

theorem hyperbolicTranslationLength_nonneg (g : SL(2, ℝ)) :
    0 ≤ hyperbolicTranslationLength g :=
  le_csInf (Set.range_nonempty _) (fun _ ⟨_, hz⟩ => hz ▸ dist_nonneg)

theorem hyperbolicTranslationLength_le_displacement (g : SL(2, ℝ)) (z : UpperHalfPlane) :
    hyperbolicTranslationLength g ≤ dist z (g • z) :=
  csInf_le (hyperbolic_displacements_bddBelow g) (Set.mem_range_self z)

theorem le_hyperbolicTranslationLength (g : SL(2, ℝ)) {a : ℝ}
    (h : ∀ z : UpperHalfPlane, a ≤ dist z (g • z)) :
    a ≤ hyperbolicTranslationLength g :=
  le_csInf (Set.range_nonempty _) (fun _ ⟨z, hz⟩ => hz ▸ h z)

theorem hyperbolicTranslationLength_eq_of_attained_lower_bound
    (g : SL(2, ℝ)) (a : ℝ) (z : UpperHalfPlane)
    (hlower : ∀ w : UpperHalfPlane, a ≤ dist w (g • w))
    (hz : dist z (g • z) = a) : hyperbolicTranslationLength g = a :=
  le_antisymm ((hyperbolicTranslationLength_le_displacement g z).trans_eq hz)
    (le_hyperbolicTranslationLength g hlower)

/-- Conjugating a matrix preserves its actual hyperbolic metric translation length. -/
theorem hyperbolicTranslationLength_conjugate (g h : SL(2, ℝ)) :
    hyperbolicTranslationLength (h * g * h⁻¹) = hyperbolicTranslationLength g := by
  have heq : Set.range (fun z : UpperHalfPlane => dist z ((h * g * h⁻¹) • z)) =
      Set.range (fun z : UpperHalfPlane => dist z (g • z)) := by
    ext a
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨h⁻¹ • z, ?_⟩
      dsimp only
      rw [← dist_smul h (h⁻¹ • z) (g • (h⁻¹ • z))]
      simp only [smul_inv_smul, mul_smul]
    · rintro ⟨z, rfl⟩
      refine ⟨h • z, ?_⟩
      dsimp only
      simp only [mul_smul, inv_smul_smul, dist_smul]
  exact congrArg sInf heq

/-- The genuine determinant-one positive diagonal matrix. -/
def hyperbolicPositiveDiagonal (a : ℝ) (ha : 0 < a) : SL(2, ℝ) :=
  ⟨!![a, 0; 0, a⁻¹], by
    simp [Matrix.det_fin_two, mul_inv_cancel₀ ha.ne']⟩

theorem hyperbolicPositiveDiagonal_coe_smul (a : ℝ) (ha : 0 < a)
    (z : UpperHalfPlane) :
    ((hyperbolicPositiveDiagonal a ha • z : UpperHalfPlane) : ℂ) = (a ^ 2 : ℝ) * (z : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  change ((a : ℂ) * (z : ℂ) + 0) / (0 * (z : ℂ) + ((a⁻¹ : ℝ) : ℂ)) = _
  simp only [add_zero, zero_mul, zero_add, Complex.ofReal_inv, div_inv_eq_mul, Complex.ofReal_pow]
  ring

theorem hyperbolicPositiveDiagonal_im (a : ℝ) (ha : 0 < a)
    (z : UpperHalfPlane) :
    (hyperbolicPositiveDiagonal a ha • z).im = a ^ 2 * z.im := by
  have hh := congrArg Complex.im (hyperbolicPositiveDiagonal_coe_smul a ha z)
  simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    UpperHalfPlane.coe_im, zero_mul, zero_add, add_zero] using hh

theorem hyperbolicPositiveDiagonal_re (a : ℝ) (ha : 0 < a)
    (z : UpperHalfPlane) :
    (hyperbolicPositiveDiagonal a ha • z).re = a ^ 2 * z.re := by
  have hh := congrArg Complex.re (hyperbolicPositiveDiagonal_coe_smul a ha z)
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    UpperHalfPlane.coe_re, zero_mul, sub_zero] using hh

private theorem hyperbolicPositiveDiagonal_log_im_dist (a : ℝ) (ha : 1 < a)
    (z : UpperHalfPlane) :
    dist (Real.log z.im) (Real.log (hyperbolicPositiveDiagonal a (by linarith) • z).im) =
      2 * Real.log a := by
  have ha0 : 0 < a := by linarith
  rw [hyperbolicPositiveDiagonal_im, Real.log_mul (pow_ne_zero 2 ha0.ne') z.im_ne_zero,
    Real.log_pow, Real.dist_eq]
  norm_num only [Nat.cast_ofNat]
  have heq : Real.log z.im - (2 * Real.log a + Real.log z.im) = -(2 * Real.log a) := by ring
  rw [heq, abs_neg, abs_of_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg ha.le))]

theorem hyperbolicPositiveDiagonal_displacement_lower_bound
    (a : ℝ) (ha : 1 < a) (z : UpperHalfPlane) :
    2 * Real.log a ≤ dist z (hyperbolicPositiveDiagonal a (by linarith) • z) := by
  rw [← hyperbolicPositiveDiagonal_log_im_dist a ha z]
  exact UpperHalfPlane.dist_log_im_le _ _

/-- The vertical line is an actual unit-speed hyperbolic axis. -/
def hyperbolicVerticalAxis (t : ℝ) : UpperHalfPlane :=
  UpperHalfPlane.mk ⟨0, Real.exp t⟩ (Real.exp_pos t)

theorem hyperbolicVerticalAxis_isometry : Isometry hyperbolicVerticalAxis :=
  UpperHalfPlane.isometry_vertical_line 0

/-- Every point of the vertical axis attains the diagonal's displacement lower bound. -/
theorem hyperbolicPositiveDiagonal_axis_displacement
    (a : ℝ) (ha : 1 < a) (t : ℝ) :
    dist (hyperbolicVerticalAxis t)
      (hyperbolicPositiveDiagonal a (by linarith) • hyperbolicVerticalAxis t) =
      2 * Real.log a := by
  rw [UpperHalfPlane.dist_of_re_eq]
  · exact hyperbolicPositiveDiagonal_log_im_dist a ha _
  · rw [hyperbolicPositiveDiagonal_re]
    simp [hyperbolicVerticalAxis]

/-- The metric infimum for the actual diagonal is attained and equals `2 log a`. -/
theorem hyperbolicTranslationLength_positiveDiagonal (a : ℝ) (ha : 1 < a) :
    hyperbolicTranslationLength (hyperbolicPositiveDiagonal a (by linarith)) = 2 * Real.log a :=
  hyperbolicTranslationLength_eq_of_attained_lower_bound _ _ (hyperbolicVerticalAxis 0)
    (hyperbolicPositiveDiagonal_displacement_lower_bound a ha)
    (hyperbolicPositiveDiagonal_axis_displacement a ha 0)

/-- The diagonal translates its genuine unit-speed vertical axis by `2 log a`. -/
theorem hyperbolicPositiveDiagonal_axis_action (a : ℝ) (ha : 0 < a) (t : ℝ) :
    hyperbolicPositiveDiagonal a ha • hyperbolicVerticalAxis t =
      hyperbolicVerticalAxis (t + 2 * Real.log a) := by
  apply UpperHalfPlane.ext_re_im
  · rw [hyperbolicPositiveDiagonal_re]
    simp [hyperbolicVerticalAxis]
  · rw [hyperbolicPositiveDiagonal_im]
    change a ^ 2 * Real.exp t = Real.exp (t + 2 * Real.log a)
    have hlog : Real.log (a ^ 2) = 2 * Real.log a := by
      simpa only [Nat.cast_ofNat] using Real.log_pow a 2
    rw [Real.exp_add, ← hlog, Real.exp_log (pow_pos ha 2), mul_comm]

/-- Matrix trace is unchanged by an actual determinant-one conjugacy. -/
theorem hyperbolic_matrix_trace_conjugate (g h : SL(2, ℝ)) :
    Matrix.trace ((h * g * h⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℝ) := by
  change Matrix.trace ((h : Matrix (Fin 2) (Fin 2) ℝ) *
    (g : Matrix (Fin 2) (Fin 2) ℝ) * ((h⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) = _
  rw [Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

@[simp] theorem hyperbolicPositiveDiagonal_trace (a : ℝ) (ha : 0 < a) :
    Matrix.trace (hyperbolicPositiveDiagonal a ha : Matrix (Fin 2) (Fin 2) ℝ) = a + a⁻¹ := by
  simp [hyperbolicPositiveDiagonal, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]

/-- Under an explicit actual positive-diagonal conjugacy, the metric
translation length has the trace formula. Existence of that conjugacy is
not an assumption hidden in the definition of length. -/
theorem hyperbolicTranslationLength_trace_of_diagonal_conjugacy
    (g h : SL(2, ℝ)) (a : ℝ) (ha : 1 < a)
    (hg : g = h * hyperbolicPositiveDiagonal a (by linarith) * h⁻¹) :
    hyperbolicTranslationLength g =
      2 * Real.arcosh (|Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℝ)| / 2) := by
  have ha0 : 0 < a := by linarith
  have htrace : Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℝ) = a + a⁻¹ := by
    rw [hg, hyperbolic_matrix_trace_conjugate, hyperbolicPositiveDiagonal_trace]
  rw [htrace, abs_of_pos (add_pos ha0 (inv_pos.mpr ha0)), ← Real.cosh_log ha0,
    Real.arcosh_cosh (Real.log_nonneg ha.le)]
  rw [hg, hyperbolicTranslationLength_conjugate, hyperbolicTranslationLength_positiveDiagonal a ha]

/-- The same explicit conjugacy supplies an attaining point for the metric
infimum, on the conjugate of the actual vertical axis. -/
theorem hyperbolicTranslationLength_attained_of_diagonal_conjugacy
    (g h : SL(2, ℝ)) (a : ℝ) (ha : 1 < a)
    (hg : g = h * hyperbolicPositiveDiagonal a (by linarith) * h⁻¹) :
    ∃ z : UpperHalfPlane, dist z (g • z) = hyperbolicTranslationLength g := by
  refine ⟨h • hyperbolicVerticalAxis 0, ?_⟩
  rw [hg, hyperbolicTranslationLength_conjugate, hyperbolicTranslationLength_positiveDiagonal a ha]
  simpa only [mul_smul, inv_smul_smul, dist_smul] using
    hyperbolicPositiveDiagonal_axis_displacement a ha 0

end Markov
