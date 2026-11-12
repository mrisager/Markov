import Markov.TraceBoundaryPath
import Markov.ChordParametrization

/-! The four normalized chords traverse the actual trace-norm boundary
without repetition on one half-open period. The positive second coordinate
assigns each axis seam to its preceding chord. -/

noncomputable section
open Set

namespace Markov

/-- A closed quarter of the global path is its normalized chord, including
the seams where the piecewise definition selects the following chord. -/
theorem traceBoundaryPath_add_eq_chordBoundarySection (i : Fin 4) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    traceBoundaryPath ((i.val : ℝ) + s) =
      chordBoundarySection (traceRotationBasis i.val) s := by
  fin_cases i
  · rcases lt_or_eq_of_le hs.2 with hlt | rfl
    · simpa only [Nat.cast_zero, zero_add, chordBoundarySection] using
        traceBoundaryPath_of_lt_one s hlt
    · convert (chordBoundarySection_seam (traceRotationBasis 0)).symm using 1
      norm_num [traceBoundaryPath, chordBoundarySection, traceRotationBasis_succ]
  · rcases lt_or_eq_of_le hs.2 with hlt | rfl
    · simpa only [Nat.cast_one, add_sub_cancel_left, chordBoundarySection] using
        traceBoundaryPath_of_one_le_of_lt_two (1 + s) (by linarith [hs.1]) (by linarith)
    · convert (chordBoundarySection_seam (traceRotationBasis 1)).symm using 1
      norm_num [traceBoundaryPath, chordBoundarySection, traceRotationBasis_succ]
  · rcases lt_or_eq_of_le hs.2 with hlt | rfl
    · simpa only [Nat.cast_ofNat, add_sub_cancel_left, chordBoundarySection] using
        traceBoundaryPath_of_two_le_of_lt_three (2 + s) (by linarith [hs.1]) (by linarith)
    · convert (chordBoundarySection_seam (traceRotationBasis 2)).symm using 1
      norm_num [traceBoundaryPath, chordBoundarySection, traceRotationBasis_succ]
  · simpa only [Nat.cast_ofNat, add_sub_cancel_left, chordBoundarySection] using
      traceBoundaryPath_of_three_le (3 + s) (by linarith [hs.1])

/-- In its own quarter frame a half-open chord has nonnegative first
coordinate and strictly positive second coordinate. -/
theorem chordBoundarySection_coord_signs (B : Module.Basis (Fin 2) ℝ TracePlane)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    0 ≤ B.coord 0 (chordBoundarySection B s) ∧
      0 < B.coord 1 (chordBoundarySection B s) := by
  have hpos : 0 < ‖(1 - s) • B 0 + s • B 1‖⁻¹ := by
    rw [← chordBasis_affinePoint]
    exact inv_pos.mpr (norm_pos_iff.mpr (basis_affineLine_ne_zero (chordBasis B) s))
  rw [chordBoundarySection_coord_zero, chordBoundarySection_coord_one]
  exact ⟨mul_nonneg hpos.le (by linarith [hs.2]), mul_pos hpos hs.1⟩

/-- The positive, half-open quarters occupy disjoint coordinate sectors. -/
theorem traceChordBoundarySection_eq_iff (i j : Fin 4) (s t : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) :
    chordBoundarySection (traceRotationBasis i.val) s =
        chordBoundarySection (traceRotationBasis j.val) t ↔ i = j ∧ s = t := by
  constructor
  · intro heq
    have hi := chordBoundarySection_coord_signs (traceRotationBasis i.val) s hs
    have hj := chordBoundarySection_coord_signs (traceRotationBasis j.val) t ht
    rw [← heq] at hj
    have hij : i = j := by
      fin_cases i <;> fin_cases j <;>
        simp only [traceRotationBasis, Function.iterate_succ_apply,
          Function.iterate_zero_apply, quarterTurnBasis_coord_zero,
          quarterTurnBasis_coord_one, neg_neg] at hi hj <;>
        first | rfl | exfalso; linarith [hi.1, hi.2, hj.1, hj.2]
    subst j
    exact ⟨rfl, chordBoundarySection_injective _ heq⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Every parameter of one half-open traversal belongs to a unique quarter
with a local parameter in `(0,1]`. -/
theorem exists_traceBoundary_quarter (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 4) :
    ∃ (i : Fin 4) (s : ℝ), s ∈ Ioc (0 : ℝ) 1 ∧ t = (i.val : ℝ) + s := by
  by_cases h1 : t ≤ 1
  · exact ⟨0, t, ⟨ht.1, h1⟩, by simp⟩
  by_cases h2 : t ≤ 2
  · exact ⟨1, t - 1, ⟨by linarith, by linarith⟩, by norm_num⟩
  by_cases h3 : t ≤ 3
  · exact ⟨2, t - 2, ⟨by linarith, by linarith⟩, by norm_num⟩
  · exact ⟨3, t - 3, ⟨by linarith, by linarith [ht.2]⟩, by norm_num⟩

/-- One full half-open period of the actual boundary path has no repeated
point. The endpoint `4` represents the omitted initial point `0`. -/
theorem traceBoundaryPath_injOn_Ioc : InjOn traceBoundaryPath (Ioc (0 : ℝ) 4) := by
  intro s hs t ht heq
  obtain ⟨i, u, hu, rfl⟩ := exists_traceBoundary_quarter s hs
  obtain ⟨j, v, hv, rfl⟩ := exists_traceBoundary_quarter t ht
  rw [traceBoundaryPath_add_eq_chordBoundarySection i u ⟨hu.1.le, hu.2⟩,
    traceBoundaryPath_add_eq_chordBoundarySection j v ⟨hv.1.le, hv.2⟩] at heq
  obtain ⟨rfl, rfl⟩ := (traceChordBoundarySection_eq_iff i j u v hu hv).mp heq
  rfl

/-- Inside one half-open period, the preimage of a path point is exactly its
given parameter. -/
theorem traceBoundaryPath_preimage_singleton_inter_Ioc (t : ℝ)
    (ht : t ∈ Ioc (0 : ℝ) 4) :
    traceBoundaryPath ⁻¹' {traceBoundaryPath t} ∩ Ioc (0 : ℝ) 4 = {t} := by
  ext s
  constructor
  · rintro ⟨hs, hsI⟩
    exact traceBoundaryPath_injOn_Ioc hsI ht hs
  · intro hs
    rcases hs with rfl
    exact ⟨rfl, ht⟩

end Markov
