import T1VKAnalyticRegion
import T1FiniteContourShift
import T1VerticalTail
import T1RieszMertensContour

/-! The finite-height contour for the actual Riesz sum in the moving
region. Both horizontal edges and the truncated right tail are bounded. -/
noncomputable section
open Complex Set MeasureTheory
namespace Markov

theorem t1_vkRiesz_integral_finite_bound {c C : ℝ} (hc : 0 < c) (hc' : c ≤ 1/4) (hC : 0 < C)
    (hZ : ∀ s : ℂ, 1-t1_vkHeightWidth c s.im ≤ s.re → t1_poleRemovedZeta s ≠ 0)
    (hB : ∀ s : ℂ, t1_vkContourLeft c s.im ≤ s.re →
      ‖t1_reciprocalZeta s‖ ≤ C*(1+|s.im|)^27)
    {x b T : ℝ} (hx : 1 ≤ x) (hb : 1 ≤ b) (hb2 : b ≤ 2) (hT : 1 ≤ T) :
    let a := t1_vkContourLeft c T
    let F := t1_rieszIntegrand t1_vkRieszOrder x t1_reciprocalZeta
    ‖∫ t : ℝ, F (t1_verticalPoint b t)‖ ≤
      (x^a*C*(3 : ℝ)^31)*(∫ t : ℝ, (1+|t|)^(-(4 : ℝ))) +
      6*(x^b*C*(3 : ℝ)^31)*T^(-(3 : ℝ)) := by
  intro a F
  have hT0 := zero_lt_one.trans_le hT
  have hx0 := zero_lt_one.trans_le hx
  have ha := t1_vkContourLeft_bounds hc hc' T
  have hab : a ≤ b := ha.2.le.trans hb
  have ha0 : (1 : ℝ)/2 ≤ a := ha.1
  have hlen : b-a ≤ 2 := by linarith
  have hregion (s : ℂ) (hRe : a ≤ s.re) (hIm : |s.im| ≤ T) :
      t1_vkContourLeft c s.im ≤ s.re :=
    (t1_vkContourLeft_mono hc.le (by rwa [abs_of_pos hT0])).trans hRe
  have hdiff : DifferentiableOn ℂ F {s : ℂ | s.re ∈ Icc a b ∧ |s.im| ≤ T} := by
    intro s hs
    exact (t1_vkRieszIntegrand_differentiableAt hc hc' hZ hx0
      (hregion s hs.1.1 hs.2)).differentiableWithinAt
  have hpoint (ξ t : ℝ) (h : t1_vkContourLeft c t ≤ ξ) :
      ‖F (t1_verticalPoint ξ t)‖ ≤ (x^ξ*C*(3 : ℝ)^31)*(1+|t|)^(-(4 : ℝ)) := by
    have hs : t1_vkContourLeft c (t1_verticalPoint ξ t).im ≤ (t1_verticalPoint ξ t).re := by
      rwa [t1_verticalPoint_re,t1_verticalPoint_im]
    simpa only [t1_verticalPoint_re,t1_verticalPoint_im,F] using
      t1_vkRieszIntegrand_norm hc hc' hC.le hB hx0 hs
  have hI : Integrable (fun t : ℝ => (1+|t|)^(-(4 : ℝ))) :=
    t1_verticalPower_integrable _ (by norm_num)
  have hleft : ‖t1_verticalTrunc F a T‖ ≤
      (x^a*C*(3 : ℝ)^31)*(∫ t : ℝ, (1+|t|)^(-(4 : ℝ))) := by
    rw [← integral_const_mul]
    apply t1_verticalTrunc_integrable_majorant hT0.le (hI.const_mul _) (fun _ => by positivity)
    intro t ht
    have hm : |t| ≤ |T| := by rw [abs_of_pos hT0]; exact abs_le.mpr ht
    exact hpoint a t (t1_vkContourLeft_mono hc.le hm)
  let H := (x^b*C*(3 : ℝ)^31)*T^(-(3 : ℝ))
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hhor (ξ t : ℝ) (hξ : ξ ∈ Icc a b) (ht : |t| = T) :
      ‖F (t1_verticalPoint ξ t)‖ ≤ H := by
    have ht' : |t| ≤ |T| := by rw [ht,abs_of_pos hT0]
    have hp := hpoint ξ t ((t1_vkContourLeft_mono hc.le ht').trans hξ.1)
    have hpow : x^ξ ≤ x^b := Real.rpow_le_rpow_of_exponent_le hx hξ.2
    have hdec : (1+|t|)^(-(4 : ℝ)) ≤ T^(-(3 : ℝ)) := calc
      _ ≤ T^(-(4 : ℝ)) := Real.rpow_le_rpow_of_nonpos hT0 (by rw [ht]; linarith) (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
    exact hp.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hC.le) (by positivity))
      hdec (by positivity) (by positivity))
  have hTrunc := t1_verticalTrunc_rect_bound hab hT0.le hdiff (H := H)
    (fun ξ hξ => ⟨hhor ξ T hξ (abs_of_pos hT0),
      hhor ξ (-T) hξ (by rw [abs_neg,abs_of_pos hT0])⟩)
  obtain ⟨hFright,hBright⟩ := t1_vkRieszIntegrand_right_strip hc hc' hb hZ hB
  have hi : VerticalIntegrable F b :=
    t1_rieszIntegrand_verticalIntegrable (by linarith : (1 : ℝ)/2 ≤ b) hx0 hC.le
      (show (27 : ℝ) < (t1_vkRieszOrder : ℝ) by norm_num [t1_vkRieszOrder])
      ⟨le_rfl,hb2⟩ hFright hBright
  have htail := t1_vertical_truncation_error hi (show 0 ≤ x^b*C*(3 : ℝ)^31 by positivity) hT0
    (fun t _ => hpoint b t ((t1_vkContourLeft_bounds hc hc' t).2.le.trans hb))
  change ‖(∫ t : ℝ, F (t1_verticalPoint b t))-t1_verticalTrunc F b T‖ ≤
    2*(x^b*C*(3 : ℝ)^31)*T^(-(3 : ℝ)) at htail
  have hbT : 2*(b-a)*H ≤ 4*H := by
    exact mul_le_mul_of_nonneg_right (by linarith) hH
  calc
    _ ≤ ‖(∫ t : ℝ, F (t1_verticalPoint b t))-t1_verticalTrunc F b T‖+
        ‖t1_verticalTrunc F b T‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := by
      rw [show 6*(x^b*C*(3 : ℝ)^31)*T^(-(3 : ℝ)) = 6*H by dsimp [H]; ring]
      have ht' : ‖(∫ t : ℝ, F (t1_verticalPoint b t))-t1_verticalTrunc F b T‖ ≤ 2*H := by
        convert htail using 1
        dsimp [H]
        ring
      linarith

end Markov
