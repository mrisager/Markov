import Markov.UpperHalfPlaneCayleyAxisSides
import Markov.HyperbolicLocalStraightening

noncomputable section
open scoped MatrixGroups
namespace Markov

private theorem positiveAxis_det (h : SL(2, ℝ)) :
    h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using h.det_coe

private theorem positiveAxis_im (h : SL(2, ℝ)) (t : ℝ) :
    (h • hyperbolicVerticalAxis t).im = Real.exp t /
      ((h 1 0)^2 * (Real.exp t)^2 + (h 1 1)^2) := by
  change (((h • hyperbolicVerticalAxis t : UpperHalfPlane) : ℂ)).im = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  simp [Complex.div_im, Complex.normSq_apply, hyperbolicVerticalAxis]
  rw [← sub_div]
  have he := positiveAxis_det h
  congr 1
  · linear_combination Real.exp t * he
  · ring

/-- An actual determinant-one matrix translating every vertical-axis point
by a positive real parameter shift has hyperbolic trace. -/
theorem hyperbolic_trace_of_positive_vertical_shift
    (h : SL(2, ℝ)) (P : ℝ) (hP : 0 < P)
    (hact : ∀ t : ℝ, h • hyperbolicVerticalAxis t = hyperbolicVerticalAxis (t + P)) :
    2 < |Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℝ)| := by
  have hden (t : ℝ) :
      (h 1 0)^2 * (Real.exp t)^2 + (h 1 1)^2 = Real.exp (-P) := by
    have he := congrArg UpperHalfPlane.im (hact t)
    rw [positiveAxis_im] at he
    change Real.exp t / _ = Real.exp (t + P) at he
    have hD : (h 1 0)^2 * (Real.exp t)^2 + (h 1 1)^2 ≠ 0 := by
      intro hzero
      rw [hzero, div_zero] at he
      exact (Real.exp_pos (t + P)).ne' he.symm
    have he' := (div_eq_iff hD).mp he
    have hx : Real.exp t = Real.exp (t + P) * Real.exp (-P) := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith only [he', hx, Real.exp_pos (t + P)]
  have h0 := hden 0
  have h1 := hden 1
  simp only [Real.exp_zero, one_pow, mul_one] at h0
  have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  have hc : h 1 0 = 0 := by
    have hm : (h 1 0)^2 * ((Real.exp (1 : ℝ))^2 - 1) = 0 := by
      nlinarith only [h0, h1]
    have hc2 : (h 1 0)^2 = 0 := (mul_eq_zero.mp hm).resolve_right (by nlinarith)
    exact sq_eq_zero_iff.mp hc2
  have hd : h 1 1 ≠ 0 := by
    intro hd
    have hdet := positiveAxis_det h
    rw [hc, hd] at hdet
    norm_num at hdet
  have hb : h 0 1 = 0 := by
    have hr := congrArg UpperHalfPlane.re (hact 0)
    rw [upperHalfPlaneSL_vertical_re] at hr
    change _ = 0 at hr
    simp only [hc, mul_zero, zero_add, Real.exp_zero, one_pow, mul_one, zero_pow (by norm_num : 2 ≠ 0)] at hr
    have hbd : h 0 1 * h 1 1 = 0 :=
      (div_eq_zero_iff.mp hr).resolve_right (pow_ne_zero 2 hd)
    exact (mul_eq_zero.mp hbd).resolve_right hd
  have had : h 0 0 * h 1 1 = 1 := by
    simpa only [hb, hc, zero_mul, sub_zero] using positiveAxis_det h
  have hne : h 0 0 ≠ h 1 1 := by
    intro heq
    have hd2 : (h 1 1)^2 = 1 := by rw [heq] at had; nlinarith only [had]
    simp only [hc, zero_pow (by norm_num : 2 ≠ 0), zero_add, hd2] at h0
    have hexp : Real.exp (-P) = Real.exp 0 := by simpa using h0.symm
    have := Real.exp_injective hexp
    linarith
  have hs : 0 < (h 0 0 - h 1 1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have ht : Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℝ) = h 0 0 + h 1 1 := by
    simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply]
  rw [ht]
  have ha := sq_abs (h 0 0 + h 1 1)
  have hn := abs_nonneg (h 0 0 + h 1 1)
  nlinarith only [hs, had, ha, hn]

/-- A genuine isometric real line with an actual positive forward deck shift
forces the shifting determinant-one matrix to be hyperbolic. -/
theorem hyperbolic_trace_of_invariant_isometric_axis
    (g : SL(2, ℝ)) (F : ℝ → UpperHalfPlane) (hF : Isometry F)
    (P : ℝ) (hP : 0 < P) (hact : ∀ t : ℝ, g • F t = F (t + P)) :
    2 < |Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℝ)| := by
  obtain ⟨A, c, hA⟩ := upperHalfPlane_locally_unit_speed_eq_conjugate_vertical F
    (fun _ => ⟨1, by norm_num, fun s _ u _ => hF.dist_eq s u⟩)
  let K : SL(2, ℝ) := A⁻¹ * g * A
  have hK : ∀ t : ℝ, K • hyperbolicVerticalAxis t = hyperbolicVerticalAxis (t + P) := by
    intro t
    have he := congrArg (fun z : UpperHalfPlane => A⁻¹ • z) (hact (t - c))
    rw [hA, hA] at he
    have htc : t - c + c = t := by ring
    have htcp : t - c + P + c = t + P := by ring
    simpa only [htc, htcp, inv_smul_smul, K, mul_smul] using he
  have ht : Matrix.trace (K : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℝ) := by
    simpa only [K, inv_inv] using hyperbolic_matrix_trace_conjugate g A⁻¹
  rw [← ht]
  exact hyperbolic_trace_of_positive_vertical_shift K P hP hK

end Markov
