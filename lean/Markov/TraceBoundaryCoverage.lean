import Markov.TraceBoundaryInjective

/-! The actual four-chord trace path covers the entire unit boundary.
The half-open parameter interval assigns every coordinate-axis seam to
the preceding quarter; the initial positive axis is therefore met at `4`.
Only basis coordinates and the norm axioms enter this coverage argument. -/

noncomputable section
open Set

namespace Markov

/-- A nonzero vector belongs to one of the four quadrants whose second
coordinate is positive and whose first coordinate is nonnegative. -/
theorem traceRotationBasis_exists_nonnegative_pos (x : TracePlane) (hx : x ≠ 0) :
    ∃ i : Fin 4, 0 ≤ (traceRotationBasis i.val).coord 0 x ∧
      0 < (traceRotationBasis i.val).coord 1 x := by
  have hrep : x = (traceBasis.coord 0 x) • traceBasis 0 +
      (traceBasis.coord 1 x) • traceBasis 1 := by
    simpa only [Module.Basis.coord_apply, Fin.sum_univ_two] using
      (traceBasis.sum_repr x).symm
  by_cases h0 : 0 ≤ traceBasis.coord 0 x
  · by_cases h1 : 0 < traceBasis.coord 1 x
    · exact ⟨0, by simpa only [traceRotationBasis_zero] using h0,
        by simpa only [traceRotationBasis_zero] using h1⟩
    · have h1le : traceBasis.coord 1 x ≤ 0 := le_of_not_gt h1
      by_cases h0eq : traceBasis.coord 0 x = 0
      · have h1ne : traceBasis.coord 1 x ≠ 0 := by
          intro h1eq
          apply hx
          simpa only [h0eq, h1eq, zero_smul, add_zero] using hrep
        have h1lt : traceBasis.coord 1 x < 0 := by
          rcases eq_or_lt_of_le h1le with h1eq | h1lt
          · exact (h1ne h1eq).elim
          · exact h1lt
        refine ⟨(⟨2, by decide⟩ : Fin 4), ?_, ?_⟩ <;>
          simp only [traceRotationBasis, Function.iterate_succ_apply,
            Function.iterate_zero_apply, quarterTurnBasis_coord_zero,
            quarterTurnBasis_coord_one] <;> linarith
      · have h0pos : 0 < traceBasis.coord 0 x := by
          rcases eq_or_lt_of_le h0 with h0eq' | h0pos
          · exact (h0eq h0eq'.symm).elim
          · exact h0pos
        refine ⟨(⟨3, by decide⟩ : Fin 4), ?_, ?_⟩ <;>
          simp only [traceRotationBasis, Function.iterate_succ_apply,
            Function.iterate_zero_apply, quarterTurnBasis_coord_zero,
            quarterTurnBasis_coord_one] <;> linarith
  · have h0lt : traceBasis.coord 0 x < 0 := lt_of_not_ge h0
    by_cases h1 : 0 ≤ traceBasis.coord 1 x
    · refine ⟨(⟨1, by decide⟩ : Fin 4), ?_, ?_⟩ <;>
        simp only [traceRotationBasis, Function.iterate_succ_apply,
            Function.iterate_zero_apply, quarterTurnBasis_coord_zero,
            quarterTurnBasis_coord_one] <;> linarith
    · have h1lt : traceBasis.coord 1 x < 0 := lt_of_not_ge h1
      refine ⟨(⟨2, by decide⟩ : Fin 4), ?_, ?_⟩ <;>
        simp only [traceRotationBasis, Function.iterate_succ_apply,
            Function.iterate_zero_apply, quarterTurnBasis_coord_zero,
            quarterTurnBasis_coord_one] <;> linarith

/-- Every actual unit vector is reached during one traversal of the
four-chord path, with the initial positive axis represented by `4`. -/
theorem traceBoundaryPath_exists_Ioc (x : TracePlane) (hx : ‖x‖ = 1) :
    ∃ t ∈ Ioc (0 : ℝ) 4, traceBoundaryPath t = x := by
  have hxne : x ≠ 0 := by
    intro hxzero
    rw [hxzero, norm_zero] at hx
    norm_num at hx
  rcases traceRotationBasis_exists_nonnegative_pos x hxne with ⟨i, h0, h1⟩
  rcases chordBoundarySection_exists_Ioc (traceRotationBasis i.val) x hx h0 h1 with
    ⟨s, hs, hsx⟩
  refine ⟨(i.val : ℝ) + s, ⟨?_, ?_⟩, ?_⟩
  · have hi : (0 : ℝ) ≤ i.val := by exact_mod_cast Nat.zero_le i.val
    linarith [hs.1]
  · have hi : (i.val : ℝ) ≤ 3 := by exact_mod_cast Nat.le_of_lt_succ i.is_lt
    linarith [hs.2]
  · rw [traceBoundaryPath_add_eq_chordBoundarySection i s ⟨hs.1.le, hs.2⟩]
    exact hsx

/-- The four actual normalized chords cover the full boundary of the
closed unit ball in the constructed trace norm. -/
theorem traceBoundaryPath_image_Ioc :
    traceBoundaryPath '' Ioc (0 : ℝ) 4 =
      frontier (Metric.closedBall (0 : TracePlane) 1) := by
  ext x
  constructor
  · rintro ⟨t, _, rfl⟩
    exact traceBoundaryPath_mem_frontier t
  · intro hx
    have hxnorm : ‖x‖ = 1 := by
      rw [frontier_closedBall (0 : TracePlane) (by norm_num : (1 : ℝ) ≠ 0)] at hx
      simpa only [Metric.mem_sphere, dist_zero_right] using hx
    exact traceBoundaryPath_exists_Ioc x hxnorm

/-- The path is onto the actual trace boundary on its single-traversal
parameter interval. -/
theorem traceBoundaryPath_surjOn :
    SurjOn traceBoundaryPath (Ioc (0 : ℝ) 4)
      (frontier (Metric.closedBall (0 : TracePlane) 1)) := by
  intro x hx
  rw [← traceBoundaryPath_image_Ioc] at hx
  exact hx

end Markov
