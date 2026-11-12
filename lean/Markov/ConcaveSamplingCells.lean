import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Endpoint and secant-cell estimates for the concave sampling argument in Lemma 9. -/

open Set MeasureTheory

namespace Markov

/-- A concave function with zero endpoint values is nonnegative on the unit interval. -/
theorem concave_zero_endpoints_nonneg {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Icc 0 1) f) (h0 : f 0 = 0) (h1 : f 1 = 0)
    {s : ℝ} (hs : s ∈ Icc 0 1) : 0 ≤ f s := by
  have key := hf.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
    (show 0 ≤ 1 - s by linarith [hs.2]) hs.1 (by ring : 1 - s + s = 1)
  simpa [smul_eq_mul, h0, h1] using key

/-- The weighted chord through two points lies below a concave function between them. -/
theorem concave_chord_lower_bound {S : Set ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ S f) {a b x : ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a < b) (hx : x ∈ Icc a b) :
    (b - x) * f a + (x - a) * f b ≤ (b - a) * f x := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hw : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    field_simp
    ring
  have key := hf.2 ha hb (div_nonneg (sub_nonneg.mpr hx.2) hba.le)
    (div_nonneg (sub_nonneg.mpr hx.1) hba.le) hw
  simp only [smul_eq_mul] at key
  have hid : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by
    field_simp
    ring
  rw [hid] at key
  have hm := mul_le_mul_of_nonneg_left key hba.le
  convert hm using 1
  field_simp

/-- The first two mesh widths are controlled by twice the first mesh value. -/
theorem concave_sampling_left_endpoint_bound {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Icc 0 1) f) (h0 : f 0 = 0) (h1 : f 1 = 0)
    {h s : ℝ} (hh : 0 < h) (hhhalf : h ≤ 1 / 2)
    (hs : s ∈ Icc 0 (2 * h)) : f s ≤ 2 * f h := by
  have hhmem : h ∈ Icc (0 : ℝ) 1 := ⟨hh.le, by linarith⟩
  have hsmem : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
  have hfh := concave_zero_endpoints_nonneg hf h0 h1 hhmem
  have hfs := concave_zero_endpoints_nonneg hf h0 h1 hsmem
  by_cases hsh : s ≤ h
  · have key := concave_chord_lower_bound hf hsmem
      (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
      (by linarith : s < 1) (show h ∈ Icc s 1 from ⟨hsh, hhmem.2⟩)
    rw [h1, mul_zero, add_zero] at key
    nlinarith [mul_nonneg hs.1 hfh]
  · have hhs : h < s := lt_of_not_ge hsh
    have key := concave_chord_lower_bound hf
      (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hsmem
      (hh.trans hhs) (show h ∈ Icc 0 s from ⟨hh.le, hhs.le⟩)
    simp only [h0, mul_zero, zero_add, sub_zero] at key
    have hmul := mul_le_mul_of_nonneg_right hs.2 hfh
    nlinarith

/-- Reflection in the midpoint preserves concavity on the unit interval. -/
theorem concave_reflect_unit_interval {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Icc 0 1) f) :
    ConcaveOn ℝ (Icc 0 1) (fun x ↦ f (1 - x)) := by
  refine ⟨convex_Icc (0 : ℝ) 1, ?_⟩
  intro x hx y hy u v hu hv huv
  have hx' : 1 - x ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hy' : 1 - y ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hy.1, hy.2]
  have key := hf.2 hx' hy' hu hv huv
  simp only [smul_eq_mul] at key ⊢
  have hid : u * (1 - x) + v * (1 - y) = 1 - (u * x + v * y) := by
    nlinarith [huv]
  simpa only [hid] using key

/-- The reflected endpoint estimate controls the final two mesh widths. -/
theorem concave_sampling_right_endpoint_bound {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Icc 0 1) f) (h0 : f 0 = 0) (h1 : f 1 = 0)
    {h s : ℝ} (hh : 0 < h) (hhhalf : h ≤ 1 / 2)
    (hs : s ∈ Icc (1 - 2 * h) 1) : f s ≤ 2 * f (1 - h) := by
  have hs' : 1 - s ∈ Icc (0 : ℝ) (2 * h) := by
    constructor <;> linarith [hs.1, hs.2]
  have key := concave_sampling_left_endpoint_bound (concave_reflect_unit_interval hf)
    (by simpa using h1) (by simpa using h0) hh hhhalf hs'
  simpa using key

/-- The chord on the cell and the preceding secant bound the cell pointwise. -/
theorem concave_sampling_cell_point_bounds {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Icc 0 1) f) {a h x : ℝ} (hh : 0 < h)
    (ha : a - h ∈ Icc 0 1) (hb : a + h ∈ Icc 0 1)
    (hx : x ∈ Icc a (a + h)) :
    ((f (a + h) - f a) / h) * (x - a) ≤ f x - f a ∧
      f x - f a ≤ ((f a - f (a - h)) / h) * (x - a) := by
  have hamem : a ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [ha.1, hb.2]
  have hxmem : x ∈ Icc (0 : ℝ) 1 :=
    ⟨hamem.1.trans hx.1, hx.2.trans hb.2⟩
  constructor
  · have key := concave_chord_lower_bound hf hamem hb
      (by linarith : a < a + h) hx
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hh).2
    nlinarith [key]
  · by_cases hax : a = x
    · simp [← hax]
    · have hax' : a < x := lt_of_le_of_ne hx.1 hax
      have key := hf.slope_anti_adjacent ha hxmem (by linarith : a - h < a) hax'
      have hden : a - (a - h) = h := by ring
      rw [hden] at key
      exact (div_le_iff₀ (sub_pos.mpr hax')).1 key

/-- Integrating a line through the start of a cell gives its triangular area. -/
theorem sampling_cell_linear_integral (a h c : ℝ) :
    (∫ x in a..a + h, c * (x - a)) = c * h ^ 2 / 2 := by
  have hi : IntervalIntegrable (fun x : ℝ ↦ x) volume a (a + h) :=
    continuous_id.intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hi (intervalIntegrable_const (c := a)),
    integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- Integral comparison on a concave cell, without any differentiability assumption. -/
theorem concave_sampling_cell_integral_bounds {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Icc 0 1) f) (hc : ContinuousOn f (Icc 0 1))
    {a h : ℝ} (hh : 0 < h)
    (ha : a - h ∈ Icc 0 1) (hb : a + h ∈ Icc 0 1) :
    (h / 2) * (f (a + h) - f a) ≤ (∫ x in a..a + h, f x) - h * f a ∧
      (∫ x in a..a + h, f x) - h * f a ≤ (h / 2) * (f a - f (a - h)) := by
  have hab : a ≤ a + h := by linarith
  have hamem : a ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [ha.1, hb.2]
  have hsub : Icc a (a + h) ⊆ Icc (0 : ℝ) 1 := fun _ hx ↦
    ⟨hamem.1.trans hx.1, hx.2.trans hb.2⟩
  have hfi : IntervalIntegrable f volume a (a + h) :=
    (hc.mono hsub).intervalIntegrable_of_Icc hab
  have hdiff : IntervalIntegrable (fun x ↦ f x - f a) volume a (a + h) :=
    hfi.sub (intervalIntegrable_const (c := f a))
  have hline (c : ℝ) : IntervalIntegrable (fun x ↦ c * (x - a)) volume a (a + h) :=
    (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have hid : (∫ x in a..a + h, f x - f a) =
      (∫ x in a..a + h, f x) - h * f a := by
    rw [intervalIntegral.integral_sub hfi (intervalIntegrable_const (c := f a)),
      intervalIntegral.integral_const]
    simp only [add_sub_cancel_left, smul_eq_mul]
  constructor
  · have key := intervalIntegral.integral_mono_on hab
      (hline ((f (a + h) - f a) / h)) hdiff
      (fun x hx ↦ (concave_sampling_cell_point_bounds hf hh ha hb hx).1)
    rw [sampling_cell_linear_integral, hid] at key
    convert key using 1
    field_simp
  · have key := intervalIntegral.integral_mono_on hab hdiff
      (hline ((f a - f (a - h)) / h))
      (fun x hx ↦ (concave_sampling_cell_point_bounds hf hh ha hb hx).2)
    rw [sampling_cell_linear_integral, hid] at key
    convert key using 1
    field_simp

end Markov
