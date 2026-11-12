import T1VKFiniteRieszContour
import T1VKContourScales

/-! The genuine smoothed Möbius sum has VK decay from the explicit
zero-free-region input, with all contour scales chosen in Lean. -/
noncomputable section
open Complex Set Filter MeasureTheory
namespace Markov

theorem t1_vkRieszMertens_eventual_bound (h : t1_VKZeroFreeRegion) :
    ∃ K d : ℝ, 0 < K ∧ 0 < d ∧ ∀ᶠ x : ℝ in atTop,
      |t1_rieszMertens t1_vkRieszOrder x| ≤ K*x^(t1_vkRieszOrder+1)*Real.exp (-d*t1_vkWeight x) := by
  obtain ⟨c,hc,hc',hZ⟩ := t1_VKZeroFreeRegion_global h
  obtain ⟨C,hC,hB⟩ := t1_vkReciprocalZeta_moving_region hc hc' hZ
  let G := ∫ t : ℝ, (1+|t|)^(-(4 : ℝ))
  let D := C*(3 : ℝ)^31*(G+6*Real.exp 1)
  let K := D/(2*Real.pi)
  have hG : 0 ≤ G := integral_nonneg (fun _ => by positivity)
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,c/16,hK,by positivity,?_⟩
  filter_upwards [t1_vkContour_eventual_scales hc hc'] with x hx
  let b := t1_vkContourRight x
  let T := t1_vkContourHeight x
  let a := t1_vkContourLeft c T
  let F := t1_rieszIntegrand t1_vkRieszOrder x t1_reciprocalZeta
  let E := x*Real.exp (-(c/16)*t1_vkWeight x)
  have hx1 := hx.1
  have hx0 := zero_lt_one.trans_le hx1
  have hT : 1 ≤ T := hx.2.1
  have hb1 : 1 ≤ b := hx.2.2.1
  have hb2 : b ≤ 2 := hx.2.2.2.1
  have hA : x^a ≤ E := hx.2.2.2.2.1
  have hBT : x^b*T^(-(3 : ℝ)) ≤ Real.exp 1*E := hx.2.2.2.2.2
  have hI := t1_vkRiesz_integral_finite_bound hc hc' hC hZ hB hx1 hb1 hb2 hT
  have hI' : ‖∫ t : ℝ, F (t1_verticalPoint b t)‖ ≤ D*E := by
    have h₂ : (x^a*C*(3 : ℝ)^31)*G ≤ (C*(3 : ℝ)^31*G)*E := by
      calc
        _ = (C*(3 : ℝ)^31*G)*x^a := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hA (by positivity)
    have h₃ : 6*(x^b*C*(3 : ℝ)^31)*T^(-(3 : ℝ)) ≤
        (6*C*(3 : ℝ)^31)*(Real.exp 1*E) := by
      calc
        _ = (6*C*(3 : ℝ)^31)*(x^b*T^(-(3 : ℝ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hBT (by positivity)
    exact hI.trans ((add_le_add h₂ h₃).trans_eq (by dsimp [D]; ring))
  obtain ⟨hFr,hBr⟩ := t1_vkRieszIntegrand_right_strip hc hc' hb1 hZ hB
  have hEq := t1_rieszMertens_integral_on_strip (by linarith : (1 : ℝ)/2 ≤ b) hb2
    (show 0 < t1_vkRieszOrder by norm_num [t1_vkRieszOrder]) hx1 hC.le
    (show (27 : ℝ) < (t1_vkRieszOrder : ℝ) by norm_num [t1_vkRieszOrder]) hFr hBr
  rw [← Real.norm_eq_abs,← Complex.norm_real,hEq]
  simp only [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hx0,abs_of_pos (show (0 : ℝ)<2 by norm_num),abs_of_pos Real.pi_pos]
  change x^t1_vkRieszOrder/(2*Real.pi)*‖∫ t : ℝ, F (t1_verticalPoint b t)‖ ≤ _
  calc
    _ ≤ x^t1_vkRieszOrder/(2*Real.pi)*(D*E) := mul_le_mul_of_nonneg_left hI' (by positivity)
    _ = K*x^(t1_vkRieszOrder+1)*Real.exp (-(c/16)*t1_vkWeight x) := by
      rw [pow_succ]
      dsimp [K,E]
      ring

end Markov
