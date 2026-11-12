import Markov.FourierIntervalBound
import Markov.TraceSections
import Markov.NormalProjectionFourier

/-! Inverse-frequency decay of the actual trace-ball indicator by integrable
line slicing and the elementary oscillatory interval estimate. -/

noncomputable section
open Set MeasureTheory FourierTransform
open scoped Pointwise RealInnerProductSpace

namespace Markov

private theorem quarter_section_phase {θ : EuclideanSpace ℝ (Fin 2)} (hθ : ‖θ‖ = 1)
    (r t s : ℝ) :
    inner ℝ (traceSectionPoint (quarterTurnNormal θ) t s) (r • θ) = (-r) * s := by
  have hd : quarterTurnNormal (quarterTurnNormal θ) = -θ := by
    ext i
    fin_cases i <;> simp
  have ho : inner ℝ (quarterTurnNormal θ) θ = 0 := by
    rw [real_inner_comm]
    exact inner_quarterTurnNormal_self θ
  simp only [traceSectionPoint, hd, inner_add_left, real_inner_smul_left,
    inner_smul_right, ho, inner_neg_left, real_inner_self_eq_norm_sq, hθ, one_pow]
  ring

/-- An explicit inverse-frequency estimate with the actual Euclidean
coordinate operator as the fixed body-size constant. -/
theorem trace_indicator_fourier_decay (ξ : EuclideanSpace ℝ (Fin 2)) (hξ : ξ ≠ 0) :
    ‖𝓕 (traceComplexBallIndicator 1) ξ‖ ≤
      (2 * ‖traceEuclideanCoordinates‖ / Real.pi) / ‖ξ‖ := by
  let θ := NormedSpace.normalize ξ
  let ν := quarterTurnNormal θ
  let R : ℝ := ‖traceEuclideanCoordinates‖
  let B : ℝ := 1 / (Real.pi * ‖ξ‖)
  let H : EuclideanSpace ℝ (Fin 2) → ℂ := fun z ↦
    Real.fourierChar (-inner ℝ z ξ) • traceComplexBallIndicator 1 z
  let g : ℝ → ℂ := normalProjection H ν
  have hθ : ‖θ‖ = 1 := NormedSpace.norm_normalize hξ
  have hν : ‖ν‖ = 1 := by
    change ‖quarterTurnNormal θ‖ = 1
    rw [norm_quarterTurnNormal, hθ]
  have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR : 0 ≤ R := norm_nonneg _
  have hHi : Integrable H :=
    (Real.fourierIntegral_convergent_iff ξ).mpr (traceComplexBallIndicator_integrable 1)
  have hgi : Integrable g := normalProjection_integrable hν hHi
  have hphase (t s : ℝ) : inner ℝ (traceSectionPoint ν t s) ξ = (-‖ξ‖) * s := by
    have key := quarter_section_phase hθ ‖ξ‖ t s
    rw [show ‖ξ‖ • θ = ξ from NormedSpace.norm_smul_normalize ξ] at key
    exact key
  have hrepr (t : ℝ) : g t =
      ∫ s : ℝ, (traceSection ν t).indicator
        (fun s ↦ (Real.fourierChar (-((-‖ξ‖) * s)) : ℂ)) s := by
    apply integral_congr_ae
    filter_upwards with s
    change Real.fourierChar (-inner ℝ (traceSectionPoint ν t s) ξ) •
      traceComplexBallIndicator 1 (traceSectionPoint ν t s) = _
    rw [hphase, Circle.smul_def, smul_eq_mul]
    classical
    by_cases hs : s ∈ traceSection ν t
    · have hx : traceSectionPoint ν t s ∈ traceEuclideanBall := hs
      simp only [traceComplexBallIndicator, one_smul, indicator_of_mem hx,
        indicator_of_mem hs, mul_one]
    · have hx : traceSectionPoint ν t s ∉ traceEuclideanBall := hs
      simp only [traceComplexBallIndicator, one_smul, indicator_of_notMem hx,
        indicator_of_notMem hs, mul_zero]
  have hbound (t : ℝ) : ‖g t‖ ≤ B := by
    rw [hrepr, integral_indicator (isClosed_traceSection ν t).measurableSet]
    by_cases hne : (traceSection ν t).Nonempty
    · have hc := isCompact_traceSection hν t
      have hab : sInf (traceSection ν t) ≤ sSup (traceSection ν t) :=
        csInf_le hc.bddBelow (hc.sSup_mem hne)
      rw [traceSection_eq_Icc hν t hne]
      simpa only [abs_neg, abs_of_pos hr] using norm_setIntegral_Icc_fourierChar_le
        (-‖ξ‖) (sInf (traceSection ν t)) (sSup (traceSection ν t)) (neg_ne_zero.mpr hr.ne') hab
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      simpa only [Measure.restrict_empty, integral_zero_measure, norm_zero] using hB
  have hzero (t : ℝ) (ht : t ∉ Icc (-R) R) : g t = 0 := by
    have hemp : traceSection ν t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro s hs
      have hi := abs_real_inner_le_norm (traceSectionPoint ν t s) ν
      rw [traceSectionPoint_inner_normal hν, hν, mul_one] at hi
      have hnorm := norm_le_trace_coordinate_norm_of_mem hs
      exact ht (abs_le.mp (hi.trans hnorm))
    rw [hrepr, hemp]
    simp
  have hmajor : Integrable ((Icc (-R) R).indicator (fun _ : ℝ ↦ B)) :=
    (integrableOn_const isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc
  have hnormmajor (t : ℝ) : ‖g t‖ ≤ (Icc (-R) R).indicator (fun _ ↦ B) t := by
    classical
    by_cases ht : t ∈ Icc (-R) R
    · rw [indicator_of_mem ht]
      exact hbound t
    · rw [indicator_of_notMem ht, hzero t ht, norm_zero]
  have hfourier : 𝓕 (traceComplexBallIndicator 1) ξ = ∫ t : ℝ, g t := by
    rw [Real.fourier_eq]
    exact integral_orientedPlaneCoordinates_double ν hν H hHi
  rw [hfourier]
  calc
    _ ≤ ∫ t : ℝ, ‖g t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (Icc (-R) R).indicator (fun _ ↦ B) t :=
      integral_mono hgi.norm hmajor hnormmajor
    _ = (2 * ‖traceEuclideanCoordinates‖ / Real.pi) / ‖ξ‖ := by
      rw [integral_indicator_const _ measurableSet_Icc, Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R)]
      simp only [smul_eq_mul]
      dsimp [R, B]
      ring

/-- The body-dependent decay constant is nonnegative and independent of the frequency. -/
theorem exists_trace_indicator_fourier_decay_constant :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : EuclideanSpace ℝ (Fin 2), ξ ≠ 0 →
      ‖𝓕 (traceComplexBallIndicator 1) ξ‖ ≤ C / ‖ξ‖ :=
  ⟨2 * ‖traceEuclideanCoordinates‖ / Real.pi, by positivity, trace_indicator_fourier_decay⟩

end Markov
