import Markov.ConcaveSampling
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

/-! The concave sampling estimate on an arbitrary compact interval. -/

noncomputable section
open Set MeasureTheory
namespace Markov

/-- Rescaling the independent variable preserves the concavity of an interval slice. -/
theorem concave_sampling_affine_unit {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ConcaveOn ℝ (Icc a b) f) :
    ConcaveOn ℝ (Icc 0 1) (fun t : ℝ ↦ f (a + (b - a) * t)) := by
  have hmem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      a + (b - a) * t ∈ Icc a b := by
    constructor <;> nlinarith [ht.1, ht.2]
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx z hz α β hα hβ hsum
  have key := hf.2 (hmem hx) (hmem hz) hα hβ hsum
  simp only [smul_eq_mul] at key ⊢
  have heq : a + (b - a) * (α * x + β * z) =
      α * (a + (b - a) * x) + β * (a + (b - a) * z) := by
    calc
      _ = (α + β) * a + (b - a) * (α * x + β * z) := by rw [hsum]; ring
      _ = _ := by ring
  rw [heq]
  exact key

/-- The exact coefficient-seven sampling inequality after affine rescaling. -/
theorem concave_sampling_interval {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : Continuous f) (hf : ConcaveOn ℝ (Icc a b) f)
    (hz : ∀ x, x ∉ Icc a b → f x = 0)
    {h : ℝ} (hh : 0 < h) (hhsmall : h < (b - a) / 8) (y : ℝ) :
    |h * (∑' n : ℤ, f (h * ((n : ℝ) + y))) - ∫ x, f x| ≤
      7 * h * (f (a + h) + f (b - h)) := by
  let L : ℝ := b - a
  let F : ℝ → ℝ := fun t ↦ f (a + L * t)
  have hL : 0 < L := sub_pos.mpr hab
  have hcF : Continuous F := hc.comp (continuous_const.add (continuous_const.mul continuous_id))
  have hfF : ConcaveOn ℝ (Icc 0 1) F := concave_sampling_affine_unit hab hf
  have hzF : ∀ t, t ∉ Icc (0 : ℝ) 1 → F t = 0 := by
    intro t ht
    apply hz
    intro hm
    apply ht
    constructor <;> dsimp [L] at * <;> nlinarith [hm.1, hm.2]
  have hδ : 0 < h / L := div_pos hh hL
  have hδsmall : h / L < 1 / 8 := by
    apply (div_lt_iff₀ hL).mpr
    dsimp [L]
    linarith
  have hsample (n : ℤ) : F ((h / L) * ((n : ℝ) + (y - a / h))) =
      f (h * ((n : ℝ) + y)) := by
    dsimp [F]
    congr 1
    field_simp
    ring
  have hsum : (∑' n : ℤ, F ((h / L) * ((n : ℝ) + (y - a / h)))) =
      ∑' n : ℤ, f (h * ((n : ℝ) + y)) := tsum_congr hsample
  have hleft : F (h / L) = f (a + h) := by
    dsimp [F]
    congr 1
    field_simp
  have hright : F (1 - h / L) = f (b - h) := by
    dsimp [F]
    congr 1
    rw [mul_sub, mul_one, mul_div_cancel₀ _ hL.ne']
    dsimp [L]
    ring
  have hint : (∫ t, F t) = L⁻¹ * ∫ x, f x := by
    calc
      (∫ t, F t) = |L⁻¹| • ∫ x, f (a + x) :=
        Measure.integral_comp_mul_left (fun x ↦ f (a + x)) L
      _ = L⁻¹ * ∫ x, f x := by
        rw [integral_add_left_eq_self]
        simp only [abs_of_pos (inv_pos.mpr hL), smul_eq_mul]
  have key := mul_le_mul_of_nonneg_left
    (concave_sampling_lemma9 hcF hfF hzF hδ hδsmall (y - a / h)) hL.le
  rw [hsum, hleft, hright, hint] at key
  have hid : L * ((h / L) * (∑' n : ℤ, f (h * ((n : ℝ) + y))) -
      L⁻¹ * ∫ x, f x) = h * (∑' n : ℤ, f (h * ((n : ℝ) + y))) - ∫ x, f x := by
    field_simp
  have hmul : L * |(h / L) * (∑' n : ℤ, f (h * ((n : ℝ) + y))) -
      L⁻¹ * ∫ x, f x| =
      |h * (∑' n : ℤ, f (h * ((n : ℝ) + y))) - ∫ x, f x| := by
    calc
      _ = |L| * |(h / L) * (∑' n : ℤ, f (h * ((n : ℝ) + y))) -
          L⁻¹ * ∫ x, f x| := by rw [abs_of_pos hL]
      _ = |L * ((h / L) * (∑' n : ℤ, f (h * ((n : ℝ) + y))) -
          L⁻¹ * ∫ x, f x)| := (abs_mul _ _).symm
      _ = _ := congrArg abs hid
  rw [hmul] at key
  convert key using 1
  field_simp

/-- Samples of a function vanishing outside any bounded interval are summable. -/
theorem sampling_interval_summable {f : ℝ → ℝ} {a b : ℝ}
    (hz : ∀ x, x ∉ Icc a b → f x = 0) {h : ℝ} (hh : 0 < h) (y : ℝ) :
    Summable (fun n : ℤ ↦ f (h * ((n : ℝ) + y))) := by
  apply summable_of_finite_support
  apply (Set.finite_Icc (⌈a / h - y⌉ : ℤ) ⌊b / h - y⌋).subset
  intro n hn
  have hmem : h * ((n : ℝ) + y) ∈ Icc a b := by
    by_contra hx
    exact hn (hz _ hx)
  constructor
  · apply Int.ceil_le.mpr
    have key : a / h ≤ (n : ℝ) + y := (div_le_iff₀ hh).mpr (by simpa only [mul_comm] using hmem.1)
    linarith
  · apply Int.le_floor.mpr
    have key : (n : ℝ) + y ≤ b / h := (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hmem.2)
    linarith

/-- The interval sampling estimate together with its explicit summability assertion. -/
theorem concave_sampling_interval_with_summability {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : Continuous f) (hf : ConcaveOn ℝ (Icc a b) f)
    (hz : ∀ x, x ∉ Icc a b → f x = 0)
    {h : ℝ} (hh : 0 < h) (hhsmall : h < (b - a) / 8) (y : ℝ) :
    Summable (fun n : ℤ ↦ f (h * ((n : ℝ) + y))) ∧
      |h * (∑' n : ℤ, f (h * ((n : ℝ) + y))) - ∫ x, f x| ≤
        7 * h * (f (a + h) + f (b - h)) :=
  ⟨sampling_interval_summable hz hh y,
    concave_sampling_interval hab hc hf hz hh hhsmall y⟩

end Markov
