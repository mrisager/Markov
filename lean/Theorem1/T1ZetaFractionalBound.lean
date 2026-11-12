import T1ZetaFractionalMellin
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Uniform norm bound for the actual analytic fractional-part remainder. -/
noncomputable section
open Filter Set MeasureTheory Complex
namespace Markov

theorem t1_zetaFractionalMellin_norm_le {s : ℂ} (hs : 0 < s.re) :
    ‖t1_zetaFractionalMellin s‖ ≤ 1/s.re := by
  rw [t1_zetaFractionalMellin_integral]
  have hpow : -s.re-1 < -1 := by linarith
  have hi := (integrableOn_Ioi_rpow_of_lt hpow (show (0 : ℝ)<1 by norm_num))
  calc
    _ ≤ ∫ x : ℝ in Ioi (1 : ℝ), x^(-s.re-1) := by
      refine norm_integral_le_of_norm_le hi ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := zero_lt_one.trans hx
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Int.fract_nonneg x),
        Complex.norm_cpow_eq_rpow_re_of_pos hx0,Complex.neg_re,Complex.add_re,Complex.one_re,
        show -(s.re+1) = -s.re-1 by ring]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) (Int.fract_lt_one x).le
    _ = 1/s.re := by
      rw [integral_Ioi_rpow_of_lt hpow (show (0 : ℝ)<1 by norm_num)]
      rw [Real.one_rpow,show -s.re-1+1 = -s.re by ring]
      ring

theorem t1_zetaFractional_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (↑(Int.fract x : ℝ) : ℂ)*(x : ℂ)^(-(s+1))) (Ioi (1 : ℝ)) := by
  have hi := integrableOn_Ioi_cpow_of_lt (a := -(s+1))
    (by simp only [neg_re,add_re,one_re]; linarith) (show (0 : ℝ)<1 by norm_num)
  have hm : Measurable (Complex.ofReal ∘ (Int.fract : ℝ → ℝ)) :=
    Complex.continuous_ofReal.measurable.comp measurable_fract
  apply hi.norm.mono' (hm.aestronglyMeasurable.mul hi.aestronglyMeasurable)
  filter_upwards with x
  change ‖(↑(Int.fract x : ℝ) : ℂ)*(x : ℂ)^(-(s+1))‖ ≤ ‖(x : ℂ)^(-(s+1))‖
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Int.fract_nonneg x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one x).le

end Markov
