import Mathlib.MeasureTheory.Measure.Stieltjes

/-! A real Stieltjes function can be assembled from two supplied Stieltjes
functions whose values agree at a seam. The resulting function takes the
left branch strictly before the seam and the right branch at and after it.
The only compatibility hypothesis is equality of the seam values. -/

noncomputable section

open Set Filter

namespace Markov

/-- The piecewise real function used to join two Stieltjes functions. -/
def stieltjesGlueValue (F G : StieltjesFunction ℝ) (a x : ℝ) : ℝ :=
  if x < a then F x else G x

theorem stieltjesGlueValue_monotone (F G : StieltjesFunction ℝ) (a : ℝ)
    (h : F a = G a) : Monotone (stieltjesGlueValue F G a) := by
  intro x y hxy
  by_cases hx : x < a
  · by_cases hy : y < a
    · simpa only [stieltjesGlueValue, if_pos hx, if_pos hy] using F.mono hxy
    · have hay : a ≤ y := le_of_not_gt hy
      simpa only [stieltjesGlueValue, if_pos hx, if_neg hy] using
        (F.mono hx.le).trans (h ▸ G.mono hay)
  · have hy : ¬ y < a := not_lt.mpr ((le_of_not_gt hx).trans hxy)
    simpa only [stieltjesGlueValue, if_neg hx, if_neg hy] using G.mono hxy

/-- Choosing the right branch at the seam gives right continuity there. -/
theorem stieltjesGlueValue_right_continuous
    (F G : StieltjesFunction ℝ) (a x : ℝ) :
    ContinuousWithinAt (stieltjesGlueValue F G a) (Ici x) x := by
  by_cases hx : x < a
  · apply (F.right_continuous x).congr_of_eventuallyEq
    · filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hx)] with y hy
      simp only [stieltjesGlueValue, if_pos hy]
    · simp only [stieltjesGlueValue, if_pos hx]
  · apply (G.right_continuous x).congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have hy' : ¬ y < a := not_lt.mpr ((le_of_not_gt hx).trans hy)
      simp only [stieltjesGlueValue, if_neg hy']
    · simp only [stieltjesGlueValue, if_neg hx]

/-- Joining two actual monotone, right-continuous functions at a common
value produces another actual Stieltjes function. -/
def stieltjesGlue (F G : StieltjesFunction ℝ) (a : ℝ) (h : F a = G a) :
    StieltjesFunction ℝ where
  toFun := stieltjesGlueValue F G a
  mono' := stieltjesGlueValue_monotone F G a h
  right_continuous' := stieltjesGlueValue_right_continuous F G a

@[simp] theorem stieltjesGlue_apply (F G : StieltjesFunction ℝ) (a : ℝ)
    (h : F a = G a) (x : ℝ) :
    stieltjesGlue F G a h x = if x < a then F x else G x := rfl

theorem stieltjesGlue_of_lt (F G : StieltjesFunction ℝ) (a : ℝ)
    (h : F a = G a) (x : ℝ) (hx : x < a) :
    stieltjesGlue F G a h x = F x := by
  simp only [stieltjesGlue_apply, if_pos hx]

theorem stieltjesGlue_of_le (F G : StieltjesFunction ℝ) (a : ℝ)
    (h : F a = G a) (x : ℝ) (hx : x ≤ a) :
    stieltjesGlue F G a h x = F x := by
  rcases hx.eq_or_lt with rfl | hx
  · simpa only [stieltjesGlue_apply, lt_self_iff_false, if_false] using h.symm
  · exact stieltjesGlue_of_lt F G a h x hx

theorem stieltjesGlue_of_ge (F G : StieltjesFunction ℝ) (a : ℝ)
    (h : F a = G a) (x : ℝ) (hx : a ≤ x) :
    stieltjesGlue F G a h x = G x := by
  simp only [stieltjesGlue_apply, if_neg (not_lt.mpr hx)]

@[simp] theorem stieltjesGlue_seam (F G : StieltjesFunction ℝ) (a : ℝ)
    (h : F a = G a) : stieltjesGlue F G a h a = G a :=
  stieltjesGlue_of_ge F G a h a le_rfl

theorem stieltjesGlue_eqOn_left (F G : StieltjesFunction ℝ) (a : ℝ)
    (h : F a = G a) : EqOn (stieltjesGlue F G a h) F (Iic a) := by
  intro x hx
  exact stieltjesGlue_of_le F G a h x hx

theorem stieltjesGlue_eqOn_right (F G : StieltjesFunction ℝ) (a : ℝ)
    (h : F a = G a) : EqOn (stieltjesGlue F G a h) G (Ici a) := by
  intro x hx
  exact stieltjesGlue_of_ge F G a h x hx

/-- An interval on the left has the original left branch's Stieltjes mass. -/
theorem stieltjesGlue_measure_Ioc_left (F G : StieltjesFunction ℝ) (a : ℝ)
    (h : F a = G a) (u v : ℝ) (hu : u ≤ a) (hv : v ≤ a) :
    (stieltjesGlue F G a h).measure (Ioc u v) = F.measure (Ioc u v) := by
  rw [StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc,
    stieltjesGlue_of_le F G a h v hv, stieltjesGlue_of_le F G a h u hu]

/-- An interval on the right has the original right branch's Stieltjes mass. -/
theorem stieltjesGlue_measure_Ioc_right (F G : StieltjesFunction ℝ) (a : ℝ)
    (h : F a = G a) (u v : ℝ) (hu : a ≤ u) (hv : a ≤ v) :
    (stieltjesGlue F G a h).measure (Ioc u v) = G.measure (Ioc u v) := by
  rw [StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc,
    stieltjesGlue_of_ge F G a h v hv, stieltjesGlue_of_ge F G a h u hu]

/-- Translate both the parameter and the value of a supplied Stieltjes
function, preserving monotonicity and right continuity. -/
def stieltjesTranslate (F : StieltjesFunction ℝ) (c d : ℝ) :
    StieltjesFunction ℝ where
  toFun x := F (x - c) + d
  mono' := by
    intro x y hxy
    exact add_le_add (F.mono (sub_le_sub_right hxy c)) le_rfl
  right_continuous' := by
    intro x
    have hc : ContinuousWithinAt (fun y : ℝ => y - c) (Ici x) x :=
      (continuous_id.sub continuous_const).continuousWithinAt
    exact ((F.right_continuous (x - c)).comp (f := fun y : ℝ => y - c) (x := x) hc
      (fun y hy => sub_le_sub_right hy c)).add continuousWithinAt_const

@[simp] theorem stieltjesTranslate_apply (F : StieltjesFunction ℝ)
    (c d x : ℝ) : stieltjesTranslate F c d x = F (x - c) + d := rfl

@[simp] theorem stieltjesTranslate_zero (F : StieltjesFunction ℝ) :
    stieltjesTranslate F 0 0 = F := by
  ext x
  simp only [stieltjesTranslate_apply, sub_zero, add_zero]

theorem stieltjesTranslate_measure_Ioc (F : StieltjesFunction ℝ)
    (c d u v : ℝ) :
    (stieltjesTranslate F c d).measure (Ioc u v) = F.measure (Ioc (u - c) (v - c)) := by
  rw [StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc]
  simp only [stieltjesTranslate_apply, add_sub_add_right_eq_sub]

end Markov
