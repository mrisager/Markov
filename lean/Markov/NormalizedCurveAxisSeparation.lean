import Markov.UpperHalfPlaneCayleyAxisSides
import Markov.UpperHalfPlaneCayleyInjective
import Markov.RealDiskCurveCrossing
import Markov.UnitDiskOppositeChord

noncomputable section
open Filter Set Topology
open scoped MatrixGroups
namespace Markov

/-- A curve uniformly following the positive vertical line cannot be disjoint
from its actual SL translate if the corresponding axes meet transversely.
The supplied disjointness therefore forces coincident axis ranges. -/
theorem normalizedCurve_axes_eq_of_intersect
    (γ : ℝ → UpperHalfPlane) (hcγ : Continuous γ)
    (κ B : ℝ) (hκ : 0 < κ)
    (hbound : ∀ t, dist (γ t) (hyperbolicVerticalAxis (κ*t)) ≤ B)
    (k : SL(2, ℝ))
    (hdisj : Disjoint (range γ) (range (fun t : ℝ => k • γ t)))
    (hinter : (range (fun t : ℝ => k • hyperbolicVerticalAxis t) ∩
      range hyperbolicVerticalAxis).Nonempty) :
    range (fun t : ℝ => k • hyperbolicVerticalAxis t) = range hyperbolicVerticalAxis := by
  by_contra hne
  have hop := upperHalfPlaneCayleySL_opposite_im_of_axes_intersect k hinter hne
  have hcim : (upperHalfPlaneCayleySLZero k).im ≠ 0 := by
    intro he
    rw [he, zero_mul] at hop
    linarith
  have hdim : (upperHalfPlaneCayleySLInfinity k).im ≠ 0 := by
    intro he
    rw [he, mul_zero] at hop
    linarith
  have hnegc : (-1 : ℂ) ≠ upperHalfPlaneCayleySLZero k := by
    intro he
    apply hcim
    rw [← he]
    norm_num
  have hnegd : (-1 : ℂ) ≠ upperHalfPlaneCayleySLInfinity k := by
    intro he
    apply hdim
    rw [← he]
    norm_num
  have hposc : (1 : ℂ) ≠ upperHalfPlaneCayleySLZero k := by
    intro he
    apply hcim
    rw [← he]
    norm_num
  have hposd : (1 : ℂ) ≠ upperHalfPlaneCayleySLInfinity k := by
    intro he
    apply hdim
    rw [← he]
    norm_num
  obtain ⟨u, v, hu0, hu1, hv0, hv1, hchord, hdet⟩ :=
    unitDisk_opposite_imaginary_chord_crossing
      (upperHalfPlaneCayleySLZero k) (upperHalfPlaneCayleySLInfinity k)
      (upperHalfPlaneCayleySLZero_norm k) (upperHalfPlaneCayleySLInfinity_norm k) hop
  obtain ⟨s, t, heq⟩ := realDiskCurves_intersect_of_transverse_endpoint_chords
    (fun t => upperHalfPlaneCayley (γ t))
    (fun t => upperHalfPlaneCayley (k • γ t))
    (continuous_upperHalfPlaneCayley.comp hcγ)
    (continuous_upperHalfPlaneCayley.comp ((isometry_smul UpperHalfPlane k).continuous.comp hcγ))
    (-1) 1 (upperHalfPlaneCayleySLZero k) (upperHalfPlaneCayleySLInfinity k)
    (upperHalfPlaneCayley_tendsto_atBot_of_dist_vertical γ κ B hκ hbound)
    (upperHalfPlaneCayley_tendsto_atTop_of_dist_vertical γ κ B hκ hbound)
    (upperHalfPlaneCayley_smul_tendsto_atBot_of_dist_vertical k γ κ B hκ hbound)
    (upperHalfPlaneCayley_smul_tendsto_atTop_of_dist_vertical k γ κ B hκ hbound)
    (fun t => upperHalfPlaneCayley_norm_lt_one (γ t))
    (fun t => upperHalfPlaneCayley_norm_lt_one (k • γ t))
    (by norm_num) (by norm_num)
    (upperHalfPlaneCayleySLZero_norm k) (upperHalfPlaneCayleySLInfinity_norm k)
    (by norm_num) hnegc hnegd hposc hposd (upperHalfPlaneCayleySLZero_ne_infinity k)
    hdet u v hu0 hu1 hv0 hv1 hchord
  exact Set.disjoint_left.mp hdisj (mem_range_self s)
    ⟨t, (upperHalfPlaneCayley_injective heq).symm⟩

/-- Actual disjoint curve translates force the corresponding full axes to
be disjoint or literally coincident. No axis simplicity premise is used. -/
theorem normalizedCurve_axes_disjoint_or_eq
    (γ : ℝ → UpperHalfPlane) (hcγ : Continuous γ)
    (κ B : ℝ) (hκ : 0 < κ)
    (hbound : ∀ t, dist (γ t) (hyperbolicVerticalAxis (κ*t)) ≤ B)
    (k : SL(2, ℝ))
    (hdisj : Disjoint (range γ) (range (fun t : ℝ => k • γ t))) :
    Disjoint (range (fun t : ℝ => k • hyperbolicVerticalAxis t))
      (range hyperbolicVerticalAxis) ∨
      range (fun t : ℝ => k • hyperbolicVerticalAxis t) = range hyperbolicVerticalAxis := by
  by_cases heq : range (fun t : ℝ => k • hyperbolicVerticalAxis t) =
      range hyperbolicVerticalAxis
  · exact Or.inr heq
  · left
    apply Set.disjoint_left.mpr
    intro z hz1 hz2
    exact heq (normalizedCurve_axes_eq_of_intersect γ hcγ κ B hκ hbound k hdisj
      ⟨z, hz1, hz2⟩)

end Markov
