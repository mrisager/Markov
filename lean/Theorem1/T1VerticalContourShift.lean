import T1RieszKernelInversion
import Mathlib.Analysis.Complex.CauchyIntegral

/-! A contour shift justified by the actual Cauchy–Goursat rectangle
identity, absolute integrability on the two vertical lines, and uniform
decay on the horizontal edges. -/
noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Interval
namespace Markov

theorem t1_horizontal_integral_tendsto_zero {F : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    {g : ℝ → ℝ} {Y : ℝ → ℝ} (hg : Tendsto g atTop (𝓝 0))
    (hb : ∀ᶠ T : ℝ in atTop, ∀ x ∈ Icc a b, ‖F (t1_verticalPoint x (Y T))‖ ≤ g T) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F (t1_verticalPoint x (Y T))) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hupper : Tendsto (fun T : ℝ => g T*(b-a)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hg.mul_const (b-a)
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hupper
  filter_upwards [hb] with T hT
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x => F (t1_verticalPoint x (Y T))) (a := a) (b := b) (C := g T) ?_
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hab),mul_comm] using h
  · intro x hx
    rw [uIoc_of_le hab] at hx
    exact hT x ⟨hx.1.le,hx.2⟩

theorem t1_vertical_integral_shift {F : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hF : DifferentiableOn ℂ F {s : ℂ | s.re ∈ Icc a b})
    (ha : VerticalIntegrable F a) (hb : VerticalIntegrable F b)
    {g : ℝ → ℝ} (hg : Tendsto g atTop (𝓝 0))
    (hd : ∀ᶠ T : ℝ in atTop, ∀ x ∈ Icc a b,
      ‖F (t1_verticalPoint x T)‖ ≤ g T ∧ ‖F (t1_verticalPoint x (-T))‖ ≤ g T) :
    (∫ t : ℝ, F (t1_verticalPoint b t)) = ∫ t : ℝ, F (t1_verticalPoint a t) := by
  have hneg := t1_horizontal_integral_tendsto_zero (Y := fun T => -T) hab hg
    (hd.mono fun _ ht x hx => (ht x hx).2)
  have hpos := t1_horizontal_integral_tendsto_zero (Y := id) hab hg
    (hd.mono fun _ ht x hx => (ht x hx).1)
  have hl := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hr := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hneg.sub hpos).add ((tendsto_const_nhds (x := I)).smul hr)).sub
    ((tendsto_const_nhds (x := I)).smul hl)
  have hrect (T : ℝ) :
      (∫ x : ℝ in a..b, F (t1_verticalPoint x (-T))) -
      (∫ x : ℝ in a..b, F (t1_verticalPoint x T)) +
      I • (∫ t : ℝ in -T..T, F (t1_verticalPoint b t)) -
      I • (∫ t : ℝ in -T..T, F (t1_verticalPoint a t)) = 0 := by
    have hC := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
      (t1_verticalPoint a (-T)) (t1_verticalPoint b T) ?_
    · simpa only [t1_verticalPoint_re,t1_verticalPoint_im] using hC
    · apply hF.mono
      intro z hz
      have hh := hz.1
      simpa only [t1_verticalPoint_re,uIcc_of_le hab] using hh
  have hlim' : Tendsto (fun T : ℝ =>
      (∫ x : ℝ in a..b, F (t1_verticalPoint x (-T))) -
      (∫ x : ℝ in a..b, F (t1_verticalPoint x T)) +
      I • (∫ t : ℝ in -T..T, F (t1_verticalPoint b t)) -
      I • (∫ t : ℝ in -T..T, F (t1_verticalPoint a t))) atTop
      (𝓝 (I • (∫ t : ℝ, F (t1_verticalPoint b t)) -
        I • (∫ t : ℝ, F (t1_verticalPoint a t)))) := by
    simpa only [id_eq,sub_self,zero_add] using hlim
  have hzero := tendsto_nhds_unique hlim'
    (tendsto_const_nhds.congr fun T => (hrect T).symm)
  exact mul_left_cancel₀ I_ne_zero (sub_eq_zero.mp hzero)

end Markov
