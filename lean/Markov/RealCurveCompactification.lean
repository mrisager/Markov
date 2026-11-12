import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.ExtendFrom
import Mathlib.Topology.Path
import Mathlib.Tactic

/-! Actual real-to-closed-interval compactification using the literal logarithmic
parameter log t - log(1-t), with literal inverse exp x/(1+exp x). The endpoint
values and continuity are proved from the actual one-sided limits. No abstract
compactification, injectivity, or separation field is assumed. -/

noncomputable section
open Set Topology Filter
namespace Markov

/-- The actual real parameter on the open unit interval. -/
def realOpenIntervalParameter (t : ℝ) : ℝ := Real.log t - Real.log (1-t)

/-- The displayed parameter is continuous at every strictly interior point. -/
theorem realOpenIntervalParameter_continuousOn :
    ContinuousOn realOpenIntervalParameter (Ioo (0 : ℝ) 1) := by
  intro t ht
  exact ((continuousAt_id.log ht.1.ne').sub
    ((continuousAt_const.sub continuousAt_id).log (sub_pos.mpr ht.2).ne')).continuousWithinAt

/-- The literal parameter tends to minus infinity at the left endpoint. -/
theorem realOpenIntervalParameter_tendsto_left :
    Tendsto realOpenIntervalParameter (𝓝[>] (0 : ℝ)) atBot := by
  have hc : ContinuousAt (fun t : ℝ => Real.log (1-t)) 0 :=
    (continuousAt_const.sub continuousAt_id).log (by norm_num)
  have hh : Tendsto (fun t : ℝ => -Real.log (1-t)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hc.tendsto.neg.mono_left nhdsWithin_le_nhds
  simpa only [realOpenIntervalParameter, sub_eq_add_neg] using
    Real.tendsto_log_nhdsGT_zero.atBot_add hh

/-- The literal parameter tends to plus infinity at the right endpoint. -/
theorem realOpenIntervalParameter_tendsto_right :
    Tendsto realOpenIntervalParameter (𝓝[<] (1 : ℝ)) atTop := by
  have hs : Tendsto (fun t : ℝ => 1-t) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun t : ℝ => 1-t) 1 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change t < 1 at ht
      exact sub_pos.mpr ht
  have hn := tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hs)
  have hc : ContinuousAt Real.log (1 : ℝ) := Real.continuousAt_log one_ne_zero
  have hh : Tendsto Real.log (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  change Tendsto (fun t : ℝ => Real.log t - Real.log (1-t)) (𝓝[<] (1 : ℝ)) atTop
  simpa only [Function.comp_def, sub_eq_add_neg, add_comm] using hn.atTop_add hh

/-- The actual inverse parameter, with values in the literal closed unit interval. -/
def realOpenIntervalInverse (x : ℝ) : unitInterval :=
  ⟨Real.exp x / (1+Real.exp x), by
    have he := Real.exp_pos x
    have hd : 0 < 1+Real.exp x := by linarith
    exact ⟨(div_pos he hd).le, (div_lt_one hd).mpr (by linarith) |>.le⟩⟩

/-- Every inverse parameter lies strictly in the open interval. -/
theorem realOpenIntervalInverse_interior (x : ℝ) :
    0 < (realOpenIntervalInverse x : ℝ) ∧ (realOpenIntervalInverse x : ℝ) < 1 := by
  have he := Real.exp_pos x
  have hd : 0 < 1+Real.exp x := by linarith
  exact ⟨div_pos he hd, (div_lt_one hd).mpr (by linarith)⟩

/-- The logarithmic parameter of the literal inverse is exactly x. -/
theorem realOpenIntervalParameter_inverse (x : ℝ) :
    realOpenIntervalParameter (realOpenIntervalInverse x : ℝ) = x := by
  have he : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have hd : 1+Real.exp x ≠ 0 := ne_of_gt (by linarith [Real.exp_pos x])
  have hs : 1-Real.exp x/(1+Real.exp x) = 1/(1+Real.exp x) := by field_simp; ring
  change Real.log (Real.exp x/(1+Real.exp x))-Real.log (1-Real.exp x/(1+Real.exp x)) = x
  rw [hs, Real.log_div he hd, Real.log_div one_ne_zero hd, Real.log_exp, Real.log_one]
  ring

/-- The actual compactified path. Its open-interval values are literally the
original curve at log t-log(1-t); its endpoint values are supplied by proved limits. -/
def realCurveCompactifiedPath (f : ℝ → ℂ) (hf : Continuous f) (a b : ℂ)
    (ha : Tendsto f atBot (𝓝 a)) (hb : Tendsto f atTop (𝓝 b)) : Path a b where
  toFun t := extendFrom (Ioo (0 : ℝ) 1) (fun s => f (realOpenIntervalParameter s)) (t : ℝ)
  continuous_toFun :=
    (continuousOn_Icc_extendFrom_Ioo (by norm_num : (0 : ℝ) ≠ 1)
      (hf.comp_continuousOn realOpenIntervalParameter_continuousOn)
      (ha.comp realOpenIntervalParameter_tendsto_left)
      (hb.comp realOpenIntervalParameter_tendsto_right)).restrict
  source' := eq_lim_at_left_extendFrom_Ioo (by norm_num : (0 : ℝ) < 1)
    (ha.comp realOpenIntervalParameter_tendsto_left)
  target' := eq_lim_at_right_extendFrom_Ioo (by norm_num : (0 : ℝ) < 1)
    (hb.comp realOpenIntervalParameter_tendsto_right)

/-- The exact displayed parameter formula at every interior point. -/
theorem realCurveCompactifiedPath_apply_of_interior (f : ℝ → ℂ) (hf : Continuous f) (a b : ℂ)
    (ha : Tendsto f atBot (𝓝 a)) (hb : Tendsto f atTop (𝓝 b))
    (t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    realCurveCompactifiedPath f hf a b ha hb t = f (Real.log (t : ℝ)-Real.log (1-(t : ℝ))) :=
  extendFrom_extends (hf.comp_continuousOn realOpenIntervalParameter_continuousOn) t ⟨ht0,ht1⟩

/-- Strict disk interior is preserved at every strictly interior interval point. -/
theorem realCurveCompactifiedPath_norm_lt_one (f : ℝ → ℂ) (hf : Continuous f) (a b : ℂ)
    (ha : Tendsto f atBot (𝓝 a)) (hb : Tendsto f atTop (𝓝 b))
    (hfn : ∀ x : ℝ, ‖f x‖ < 1) (t : unitInterval)
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    ‖realCurveCompactifiedPath f hf a b ha hb t‖ < 1 := by
  rw [realCurveCompactifiedPath_apply_of_interior f hf a b ha hb t ht0 ht1]
  exact hfn _

/-- The image of the actual open interval is exactly the original real-curve range. -/
theorem realCurveCompactifiedPath_interior_range (f : ℝ → ℂ) (hf : Continuous f) (a b : ℂ)
    (ha : Tendsto f atBot (𝓝 a)) (hb : Tendsto f atTop (𝓝 b)) :
    realCurveCompactifiedPath f hf a b ha hb ''
      {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} = range f := by
  ext z
  constructor
  · rintro ⟨t,⟨ht0,ht1⟩,rfl⟩
    refine ⟨realOpenIntervalParameter t, ?_⟩
    exact (realCurveCompactifiedPath_apply_of_interior f hf a b ha hb t ht0 ht1).symm
  · rintro ⟨x,rfl⟩
    obtain ⟨ht0,ht1⟩ := realOpenIntervalInverse_interior x
    refine ⟨realOpenIntervalInverse x,⟨ht0,ht1⟩,?_⟩
    rw [realCurveCompactifiedPath_apply_of_interior f hf a b ha hb _ ht0 ht1]
    exact congrArg f (realOpenIntervalParameter_inverse x)

/-- With unit endpoint limits, the entire actual compactified path is in the
closed unit disk. No injectivity of the real curve or compactification is asserted. -/
theorem realCurveCompactifiedPath_norm_le_one (f : ℝ → ℂ) (hf : Continuous f) (a b : ℂ)
    (ha : Tendsto f atBot (𝓝 a)) (hb : Tendsto f atTop (𝓝 b))
    (hfn : ∀ x : ℝ, ‖f x‖ < 1) (han : ‖a‖=1) (hbn : ‖b‖=1) (t : unitInterval) :
    ‖realCurveCompactifiedPath f hf a b ha hb t‖ ≤ 1 := by
  by_cases ht0 : t=0
  · subst t; simpa only [Path.source] using han.le
  by_cases ht1 : t=1
  · subst t; simpa only [Path.target] using hbn.le
  apply (realCurveCompactifiedPath_norm_lt_one f hf a b ha hb hfn t _ _).le
  · exact lt_of_le_of_ne t.property.1 (fun h => ht0 (Subtype.ext h.symm))
  · exact lt_of_le_of_ne t.property.2 (fun h => ht1 (Subtype.ext h))

end Markov
