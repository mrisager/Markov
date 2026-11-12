import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics

/-! Integrable polynomial majorants on the whole real vertical parameter. -/
noncomputable section
open Filter Set MeasureTheory
namespace Markov

theorem t1_verticalPower_integrable (p : ℝ) (hp : p < -1) :
    Integrable (fun t : ℝ => (1+|t|)^p) := by
  let f := fun t : ℝ => (1+|t|)^p
  have hcont : Continuous f := by
    dsimp only [f]
    exact (continuous_const.add continuous_abs).rpow_const (fun t =>
      Or.inl (show (1 : ℝ)+|t| ≠ 0 by positivity))
  have hplus : IntegrableOn f (Ioi (1 : ℝ)) := by
    have h := integrableOn_Ioi_rpow_of_lt hp (show (0 : ℝ)<1 by norm_num)
    apply h.mono' hcont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hnorm : ‖f t‖ = (1+t)^p := by
      simp only [f,abs_of_pos ht0,Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (1 : ℝ)+t) p)]
    rw [hnorm]
    exact Real.rpow_le_rpow_of_nonpos ht0 (by linarith) (by linarith)
  have hminus : IntegrableOn f (Iio (-1 : ℝ)) := by
    have h := (MeasurePreserving.integrableOn_comp_preimage
      (Measure.measurePreserving_neg (volume : Measure ℝ))
      (Homeomorph.neg ℝ).measurableEmbedding).2 hplus
    have hs : (fun t : ℝ => -t) ⁻¹' Ioi (1 : ℝ) = Iio (-1 : ℝ) := by
      ext t
      simp only [mem_preimage,mem_Ioi,mem_Iio]
      constructor <;> intro ht <;> linarith
    simpa only [Function.comp_def,f,abs_neg,hs] using h
  exact integrable_iff_integrableAtFilter_atBot_atTop.mpr
    ⟨⟨⟨Iio (-1),Iio_mem_atBot _,hminus⟩,⟨Ioi 1,Ioi_mem_atTop _,hplus⟩⟩,
      hcont.locallyIntegrable⟩

end Markov
