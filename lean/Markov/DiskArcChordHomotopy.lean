import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic

noncomputable section
open Set Metric
namespace Markov

/-- The literal endpoint chord of a complex disk arc. -/
def diskArcChord (f : unitInterval → ℂ) (t : unitInterval) : ℂ :=
  (1 - (t : ℝ)) • f 0 + (t : ℝ) • f 1

/-- Actual affine interpolation of an arc with its endpoint chord. -/
def diskArcChordHomotopy (f : unitInterval → ℂ) (s t : unitInterval) : ℂ :=
  (1 - (s : ℝ)) • f t + (s : ℝ) • diskArcChord f t

theorem diskArcChordHomotopy_continuous
    (f : unitInterval → ℂ) (hf : Continuous f) :
    Continuous (fun st : unitInterval × unitInterval => diskArcChordHomotopy f st.1 st.2) := by
  dsimp [diskArcChordHomotopy, diskArcChord]
  fun_prop

theorem diskArcChordHomotopy_fixed_endpoints (f : unitInterval → ℂ)
    (s t : unitInterval) (ht : t = 0 ∨ t = 1) : diskArcChordHomotopy f s t = f t := by
  rcases ht with rfl | rfl <;> simp [diskArcChordHomotopy, diskArcChord, sub_smul]

theorem diskArcChord_norm_lt
    (f : unitInterval → ℂ) (h0 : ‖f 0‖ = 1) (h1 : ‖f 1‖ = 1)
    (hne : f 0 ≠ f 1) (t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    ‖diskArcChord f t‖ < 1 := by
  exact norm_combo_lt_of_ne h0.le h1.le hne (sub_pos.mpr ht1) ht0 (by ring)

theorem diskArcChordHomotopy_norm_lt
    (f : unitInterval → ℂ) (h0 : ‖f 0‖ = 1) (h1 : ‖f 1‖ = 1)
    (hne : f 0 ≠ f 1)
    (hinside : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → ‖f t‖ < 1)
    (s t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    ‖diskArcChordHomotopy f s t‖ < 1 := by
  have hf : f t ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball_zero_iff] using hinside t ht0 ht1
  have hc : diskArcChord f t ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball_zero_iff] using diskArcChord_norm_lt f h0 h1 hne t ht0 ht1
  simpa only [mem_ball_zero_iff] using (show diskArcChordHomotopy f s t ∈ ball (0 : ℂ) 1 from
    (convex_ball (0 : ℂ) 1) hf hc (sub_nonneg.mpr s.property.2) s.property.1 (by ring))

private theorem interval_interior_of_not_end (t : unitInterval) (ht : ¬ (t = 0 ∨ t = 1)) :
    0 < (t : ℝ) ∧ (t : ℝ) < 1 := by
  have h0 : (t : ℝ) ≠ 0 := fun h => ht (Or.inl (Subtype.ext h))
  have h1 : (t : ℝ) ≠ 1 := fun h => ht (Or.inr (Subtype.ext h))
  exact ⟨lt_of_le_of_ne t.property.1 h0.symm, lt_of_le_of_ne t.property.2 h1⟩

/-- On the square boundary the two affine arc-to-chord interpolations remain
apart. Only the actual disk-interior and distinct endpoint hypotheses are used;
no disjointness of the full interpolated arcs or separation theorem is assumed. -/
theorem diskArcChordHomotopy_boundary_ne
    (f g : unitInterval → ℂ)
    (hf0 : ‖f 0‖ = 1) (hf1 : ‖f 1‖ = 1) (hfn : f 0 ≠ f 1)
    (hg0 : ‖g 0‖ = 1) (hg1 : ‖g 1‖ = 1) (hgn : g 0 ≠ g 1)
    (hfi : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → ‖f t‖ < 1)
    (hgi : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → ‖g t‖ < 1)
    (hend : ∀ t u : unitInterval, (t = 0 ∨ t = 1) → (u = 0 ∨ u = 1) → f t ≠ g u)
    (s t u : unitInterval) (hb : (t = 0 ∨ t = 1) ∨ (u = 0 ∨ u = 1)) :
    diskArcChordHomotopy f s t ≠ diskArcChordHomotopy g s u := by
  by_cases ht : t = 0 ∨ t = 1
  · rw [diskArcChordHomotopy_fixed_endpoints f s t ht]
    by_cases hu : u = 0 ∨ u = 1
    · rw [diskArcChordHomotopy_fixed_endpoints g s u hu]
      exact hend t u ht hu
    · obtain ⟨hu0, hu1⟩ := interval_interior_of_not_end u hu
      have hg := diskArcChordHomotopy_norm_lt g hg0 hg1 hgn hgi s u hu0 hu1
      have hf : ‖f t‖ = 1 := by rcases ht with rfl | rfl; exact hf0; exact hf1
      intro he
      have hnorm := congrArg norm he
      linarith
  · have hu := hb.resolve_left ht
    rw [diskArcChordHomotopy_fixed_endpoints g s u hu]
    obtain ⟨ht0, ht1⟩ := interval_interior_of_not_end t ht
    have hf := diskArcChordHomotopy_norm_lt f hf0 hf1 hfn hfi s t ht0 ht1
    have hg : ‖g u‖ = 1 := by rcases hu with rfl | rfl; exact hg0; exact hg1
    intro he
    have hnorm := congrArg norm he
    linarith

end Markov
