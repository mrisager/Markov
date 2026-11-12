import Markov.AngularNormals
import Mathlib.MeasureTheory.Measure.Stieltjes

/-! Lebesgue–Stieltjes turn measure for a supplied angle lift.

For `F : StieltjesFunction ℝ`, the module computes interval masses,
atoms and finite restrictions. A parameter period with increment `2 * π`
has total mass `2 * π`. Its left endpoint is excluded and its right
endpoint is included, so the seam atom is counted once.

The normal-diameter estimate takes angular containment as a hypothesis.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Markov

/-- The genuine Lebesgue–Stieltjes measure of a supplied angle lift. -/
def angleTurnMeasure (F : StieltjesFunction ℝ) : Measure ℝ := F.measure

@[simp] theorem angleTurnMeasure_Ioc (F : StieltjesFunction ℝ) (a b : ℝ) :
    angleTurnMeasure F (Ioc a b) = ENNReal.ofReal (F b - F a) :=
  F.measure_Ioc a b

@[simp] theorem angleTurnMeasure_Ioo (F : StieltjesFunction ℝ) (a b : ℝ) :
    angleTurnMeasure F (Ioo a b) = ENNReal.ofReal (Function.leftLim F b - F a) :=
  F.measure_Ioo

@[simp] theorem angleTurnMeasure_Icc (F : StieltjesFunction ℝ) (a b : ℝ) :
    angleTurnMeasure F (Icc a b) = ENNReal.ofReal (F b - Function.leftLim F a) :=
  F.measure_Icc a b

/-- An atom's mass is the jump of the angle lift, including a possible
left discontinuity rather than an arbitrarily assigned atomic weight. -/
@[simp] theorem angleTurnMeasure_singleton (F : StieltjesFunction ℝ) (x : ℝ) :
    angleTurnMeasure F {x} = ENNReal.ofReal (F x - Function.leftLim F x) :=
  F.measure_singleton x

theorem angleTurnMeasure_Ioc_toReal (F : StieltjesFunction ℝ) (a b : ℝ)
    (hab : a ≤ b) :
    (angleTurnMeasure F (Ioc a b)).toReal = F b - F a := by
  rw [angleTurnMeasure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (F.mono hab))]

theorem angleTurnMeasure_Ioo_toReal (F : StieltjesFunction ℝ) (a b : ℝ)
    (hab : a < b) :
    (angleTurnMeasure F (Ioo a b)).toReal = Function.leftLim F b - F a := by
  rw [angleTurnMeasure_Ioo, ENNReal.toReal_ofReal
    (sub_nonneg.mpr (F.mono.le_leftLim hab))]

theorem angleTurnMeasure_singleton_toReal (F : StieltjesFunction ℝ) (x : ℝ) :
    (angleTurnMeasure F {x}).toReal = F x - Function.leftLim F x := by
  rw [angleTurnMeasure_singleton, ENNReal.toReal_ofReal
    (sub_nonneg.mpr (F.mono.leftLim_le le_rfl))]

/-- No atom occurs exactly at the continuity points of the supplied
right-continuous angle lift. -/
theorem angleTurnMeasure_singleton_eq_zero_iff (F : StieltjesFunction ℝ) (x : ℝ) :
    angleTurnMeasure F {x} = 0 ↔ ContinuousAt F x := by
  rw [angleTurnMeasure_singleton, ENNReal.ofReal_eq_zero,
    F.mono.continuousAt_iff_leftLim_eq_rightLim, F.rightLim_eq]
  have hle : Function.leftLim F x ≤ F x := F.mono.leftLim_le le_rfl
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Every bounded parameter set has finite turn, even if the full lift
has infinitely many periods and hence unbounded total turn. -/
theorem angleTurnMeasure_lt_top_of_subset_Icc (F : StieltjesFunction ℝ)
    (a b : ℝ) (S : Set ℝ) (hS : S ⊆ Icc a b) :
    angleTurnMeasure F S < ∞ := by
  apply (measure_mono hS).trans_lt
  rw [angleTurnMeasure_Icc]
  exact ENNReal.ofReal_lt_top

/-- The measure on a bounded parameter interval. The convention `(a,b]`
retains a jump at `b` and omits a jump at `a`. -/
def angleTurnMeasureOn (F : StieltjesFunction ℝ) (a b : ℝ) : Measure ℝ :=
  (angleTurnMeasure F).restrict (Ioc a b)

@[simp] theorem angleTurnMeasureOn_univ (F : StieltjesFunction ℝ) (a b : ℝ) :
    angleTurnMeasureOn F a b univ = ENNReal.ofReal (F b - F a) := by
  rw [angleTurnMeasureOn, Measure.restrict_apply_univ, angleTurnMeasure_Ioc]

instance angleTurnMeasureOn_isFiniteMeasure (F : StieltjesFunction ℝ) (a b : ℝ) :
    IsFiniteMeasure (angleTurnMeasureOn F a b) where
  measure_univ_lt_top := by
    rw [angleTurnMeasureOn_univ]
    exact ENNReal.ofReal_lt_top

theorem angleTurnMeasureOn_apply_of_subset (F : StieltjesFunction ℝ) (a b : ℝ)
    (S : Set ℝ) (hS : S ⊆ Ioc a b) :
    angleTurnMeasureOn F a b S = angleTurnMeasure F S :=
  Measure.restrict_eq_self _ hS

theorem angleTurnMeasureOn_singleton (F : StieltjesFunction ℝ) (a b x : ℝ)
    (hx : x ∈ Ioc a b) :
    angleTurnMeasureOn F a b {x} = ENNReal.ofReal (F x - Function.leftLim F x) := by
  rw [angleTurnMeasureOn_apply_of_subset F a b {x} (singleton_subset_iff.mpr hx),
    angleTurnMeasure_singleton]

/-- Finite collections of angle jumps consume at most the interval's
actual Stieltjes mass. This can be used only after genuine lower jump
estimates have been proved. -/
theorem sum_angle_jumps_le_interval_turn (F : StieltjesFunction ℝ)
    (a b : ℝ) (s : Finset ℝ) (hs : ∀ x ∈ s, x ∈ Ioc a b) :
    ∑ x ∈ s, ENNReal.ofReal (F x - Function.leftLim F x) ≤
      ENNReal.ofReal (F b - F a) := by
  simp_rw [← angleTurnMeasure_singleton]
  rw [sum_measure_singleton, ← angleTurnMeasure_Ioc]
  exact measure_mono (by simpa only [Finset.mem_coe] using hs)

/-- For a cyclic angle lift, one half-open fundamental interval has
total turn `2 * π`. The cyclic lift itself remains an input. -/
theorem angleTurnMeasureOn_univ_of_period (F : StieltjesFunction ℝ) (p a : ℝ)
    (hperiod : ∀ t : ℝ, F (t + p) = F t + 2 * Real.pi) :
    angleTurnMeasureOn F a (a + p) univ = ENNReal.ofReal (2 * Real.pi) := by
  rw [angleTurnMeasureOn_univ, hperiod]
  congr 1
  ring

/-- A periodic lift gives the same turn to intervals shifted by one
parameter period. This statement includes endpoint jumps. -/
theorem angleTurnMeasure_Ioc_add_period (F : StieltjesFunction ℝ) (p a b : ℝ)
    (hperiod : ∀ t : ℝ, F (t + p) = F t + 2 * Real.pi) :
    angleTurnMeasure F (Ioc (a + p) (b + p)) = angleTurnMeasure F (Ioc a b) := by
  rw [angleTurnMeasure_Ioc, angleTurnMeasure_Ioc, hperiod, hperiod]
  congr 1
  ring

/-- The genuine circle-valued curve determined by the supplied lift has
diameter bounded by its interval turn mass, measured in radians. -/
theorem diam_circleNormal_angleLift_image_le_interval_turn
    (F : StieltjesFunction ℝ) (a b : ℝ) (hab : a ≤ b) :
    Metric.diam ((fun t : ℝ => circleNormal (F t)) '' Icc a b) ≤
      (angleTurnMeasure F (Ioc a b)).toReal := by
  rw [angleTurnMeasure_Ioc_toReal F a b hab]
  apply diam_le_angular_width_of_subset_circleNormal_image _ (F a) (F b) (F.mono hab)
  rintro n ⟨t, ht, rfl⟩
  exact ⟨F t, ⟨F.mono ht.1, F.mono ht.2⟩, rfl⟩

/-- Application to actual support normals requires the explicit geometric
identification with the supplied lift's angle interval. -/
theorem normalsOn_diam_le_interval_turn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Module.Basis (Fin 2) ℝ E) (S : Set E)
    (F : StieltjesFunction ℝ) (a b : ℝ) (hab : a ≤ b)
    (harc : normalsOn C S ⊆ circleNormal '' Icc (F a) (F b)) :
    Metric.diam (normalsOn C S) ≤ (angleTurnMeasure F (Ioc a b)).toReal := by
  rw [angleTurnMeasure_Ioc_toReal F a b hab]
  exact normalsOn_diam_le_angular_width C S (F a) (F b) (F.mono hab) harc

end Markov
