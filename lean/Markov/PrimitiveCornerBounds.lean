import Markov.TraceBirthCornerBounds
import Markov.AxisSelectedValues
import Markov.PrimitiveBirthCoverage
import Markov.CutoffArcs

/-! The quantitative corner lower estimate of v1 Theorem 2(ii) for
the trace norm and its boundary normal-turn measure. -/

noncomputable section
open Set MeasureTheory

namespace Markov

/-- Every primitive direction has the actual exponential corner-atom
lower bound, including all four seed axes and quadrant seams. -/
theorem primitive_trace_atom_exp_lower (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    2 * ‖intVector traceBasis p‖ * Real.exp (-‖intVector traceBasis p‖) /
        (‖traceBasis 0‖ + ‖traceBasis 1‖) ^ 2 ≤
      (traceBoundaryTurn {NormedSpace.normalize (intVector traceBasis p)}).toReal := by
  rcases primitive_quadrant_seed_or_birth p hp with ⟨k, rfl⟩ | ⟨k, u, v, M, N, h, rfl⟩
  · exact trace_axis_atom_exp_lower k
  · exact h.trace_birth_atom_exp_lower k

/-- One explicit positive coefficient in the uniform cutoff estimate. -/
def traceCornerLowerConstant : ℝ :=
  2 * traceAxisLength / (‖traceBasis 0‖ + ‖traceBasis 1‖) ^ 2

theorem traceCornerLowerConstant_pos : 0 < traceCornerLowerConstant := by
  exact div_pos (mul_pos (by norm_num) traceAxisLength_pos)
    (sq_pos_of_pos traceBasis_norm_sum_pos)

/-- Theorem 2(ii)'s height-cutoff scale for every actual primitive corner.
The cutoff is real, and no compatibility or support-evaluation hypothesis remains. -/
theorem primitive_trace_atom_height_lower (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2)
    (H : ℝ) (hH : intHeight p ≤ H) :
    traceCornerLowerConstant * Real.exp (-(2 * traceAxisLength * H)) ≤
      (traceBoundaryTurn {NormedSpace.normalize (intVector traceBasis p)}).toReal := by
  have hlo := traceAxisLength_le_norm_intVector p hp
  have hhi : ‖intVector traceBasis p‖ ≤ 2 * traceAxisLength * H :=
    (tracePlane_norm_intVector_le_height p).trans
      (mul_le_mul_of_nonneg_left hH (mul_nonneg (by norm_num) traceAxisLength_pos.le))
  have he := Real.exp_le_exp.mpr (neg_le_neg hhi)
  apply le_trans _ (primitive_trace_atom_exp_lower p hp)
  unfold traceCornerLowerConstant
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hlo (by norm_num)) he
    (Real.exp_pos _).le (mul_nonneg (by norm_num) (norm_nonneg _))

/-- The stronger height times exponential-length lower scale quoted after
Theorem 2 also holds for the actual constructed trace boundary. This is the
lower bound only, not the two-sided comparison or the complement tail. -/
theorem primitive_trace_atom_height_exp_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℤ × ℤ), IsCoprime p.1 p.2 →
      c * intHeight p * Real.exp (-‖intVector traceBasis p‖) ≤
        (traceBoundaryTurn {NormedSpace.normalize (intVector traceBasis p)}).toReal := by
  obtain ⟨d, hd, hbound⟩ := tracePlane_exists_height_lower_bound
  refine ⟨2 * d / (‖traceBasis 0‖ + ‖traceBasis 1‖) ^ 2,
    div_pos (mul_pos (by norm_num) hd) (sq_pos_of_pos traceBasis_norm_sum_pos), ?_⟩
  intro p hp
  apply le_trans _ (primitive_trace_atom_exp_lower p hp)
  calc
    _ = (2 * (d * intHeight p) * Real.exp (-‖intVector traceBasis p‖)) /
        (‖traceBasis 0‖ + ‖traceBasis 1‖) ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbound p) (by norm_num)) (Real.exp_pos _).le)
      (sq_nonneg _)

/-- The actual finite integer cutoff has uniformly positive corner atoms. -/
theorem trace_cutoff_corner_atom_lower (H : ℕ) (x : TracePlane)
    (hx : x ∈ cutoffCorners traceBasis H) :
    traceCornerLowerConstant * Real.exp (-(2 * traceAxisLength * H)) ≤
      (traceBoundaryTurn {x}).toReal := by
  classical
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  have h := (mem_primitiveDirectionsUpTo H p).mp hp
  exact primitive_trace_atom_height_lower p h.1 H h.2

/-- Measure-valued form of the finite-cutoff corner estimate. -/
theorem trace_cutoff_corner_atom_lower_measure (H : ℕ) (x : TracePlane)
    (hx : x ∈ cutoffCorners traceBasis H) :
    ENNReal.ofReal (traceCornerLowerConstant * Real.exp (-(2 * traceAxisLength * H))) ≤
      traceBoundaryTurn {x} := by
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
    (trace_cutoff_corner_atom_lower H x hx)

end Markov
