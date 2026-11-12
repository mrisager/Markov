import T1VerticalPower
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Quantitative tail of a vertical integral with a fourth-power
majorant. All integral endpoints and reflection are explicit. -/
noncomputable section
open Filter Set MeasureTheory
namespace Markov

theorem t1_Ioi_norm_integral_le_fourth_tail {f : ℝ → ℂ} {C T : ℝ}
    (hC : 0 ≤ C) (hT : 0 < T)
    (hb : ∀ t : ℝ, T < t → ‖f t‖ ≤ C*(1+|t|)^(-(4 : ℝ))) :
    ‖∫ t : ℝ in Ioi T, f t‖ ≤ C*T^(-(3 : ℝ)) := by
  have he : -(4 : ℝ) < -1 := by norm_num
  have hi := (integrableOn_Ioi_rpow_of_lt he hT).const_mul C
  calc
    _ ≤ ∫ t : ℝ in Ioi T, C*t^(-(4 : ℝ)) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 := hT.trans ht
      apply (hb t ht).trans
      rw [abs_of_pos ht0]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos ht0 (by linarith) (by norm_num)) hC
    _ = C*(T^(-(3 : ℝ))/3) := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt he hT,show -(4 : ℝ)+1 = -3 by norm_num]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (div_le_self (Real.rpow_nonneg hT.le _) (by norm_num)) hC

theorem t1_Iio_norm_integral_le_fourth_tail {f : ℝ → ℂ} {C T : ℝ}
    (hC : 0 ≤ C) (hT : 0 < T)
    (hb : ∀ t : ℝ, t < -T → ‖f t‖ ≤ C*(1+|t|)^(-(4 : ℝ))) :
    ‖∫ t : ℝ in Iio (-T), f t‖ ≤ C*T^(-(3 : ℝ)) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding (fun t => f (-t)) (Ioi T)
  have hset : (fun t : ℝ => -t) ⁻¹' Ioi T = Iio (-T) := by
    ext t
    simp only [mem_preimage,mem_Ioi,mem_Iio]
    constructor <;> intro ht <;> linarith
  simp only [hset,neg_neg] at h
  rw [h]
  apply t1_Ioi_norm_integral_le_fourth_tail hC hT
  intro t ht
  simpa only [abs_neg] using hb (-t) (by linarith)

theorem t1_vertical_truncation_error {f : ℝ → ℂ} {C T : ℝ}
    (hf : Integrable f) (hC : 0 ≤ C) (hT : 0 < T)
    (hb : ∀ t : ℝ, T < |t| → ‖f t‖ ≤ C*(1+|t|)^(-(4 : ℝ))) :
    ‖(∫ t : ℝ, f t)-(∫ t : ℝ in -T..T, f t)‖ ≤ 2*C*T^(-(3 : ℝ)) := by
  have hl := t1_Iio_norm_integral_le_fourth_tail hC hT (f := f) (fun t ht =>
    hb t (by rw [abs_of_neg (by linarith)]; linarith))
  have hr := t1_Ioi_norm_integral_le_fourth_tail hC hT (f := f) (fun t ht =>
    hb t (ht.trans_le (le_abs_self _)))
  rw [← integral_Iic_eq_integral_Iio] at hl
  have hInt := intervalIntegral.integral_Iic_sub_Iic (hf.integrableOn (s := Iic (-T)))
    (hf.integrableOn (s := Iic T))
  have hFull := intervalIntegral.integral_Iic_add_Ioi (hf.integrableOn (s := Iic T))
    (hf.integrableOn (s := Ioi T))
  rw [← hFull,← hInt]
  have he : ((∫ t : ℝ in Iic T, f t)+(∫ t : ℝ in Ioi T, f t)) -
      ((∫ t : ℝ in Iic T, f t)-(∫ t : ℝ in Iic (-T), f t)) =
      (∫ t : ℝ in Iic (-T), f t)+(∫ t : ℝ in Ioi T, f t) := by abel
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hl hr).trans_eq (by ring))

end Markov
