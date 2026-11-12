import Markov.PrimitiveCornerBounds
import Markov.RealCutoffCorners

/-! The real-cutoff corner lower estimate in v1 Theorem 2(ii), for the
constructed trace norm. This does not assert the complementary tail in
Theorem 2(i), or identify the norm with the modular punctured-torus norm. -/

noncomputable section
open Set MeasureTheory

namespace Markov

/-- Every actual primitive trace corner has strictly positive turn mass. -/
theorem primitive_trace_atom_pos (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    0 < (traceBoundaryTurn {NormedSpace.normalize (intVector traceBasis p)}).toReal := by
  have hl : 0 < ‖intVector traceBasis p‖ :=
    traceAxisLength_pos.trans_le (traceAxisLength_le_norm_intVector p hp)
  exact (div_pos (mul_pos (mul_pos (by norm_num) hl) (Real.exp_pos _))
    (sq_pos_of_pos traceBasis_norm_sum_pos)).trans_le (primitive_trace_atom_exp_lower p hp)

/-- Uniform real-cutoff lower bound for the actual corner atom. -/
theorem trace_real_cutoff_corner_atom_lower (H : ℝ) (x : TracePlane)
    (hx : x ∈ realCutoffCorners traceBasis H) :
    traceCornerLowerConstant * Real.exp (-(2 * traceAxisLength * H)) ≤
      (traceBoundaryTurn {x}).toReal := by
  obtain ⟨p, hp, hH, rfl⟩ := hx
  exact primitive_trace_atom_height_lower p hp H hH

/-- Theorem 2(ii)'s positive-constant formulation, for the actual trace
boundary and the exact real primitive-height cutoff. The statement uses
the boundary Borel measure itself, rather than an assumed turn function. -/
theorem traceBoundary_corner_lower_estimate :
    ∃ m K : ℝ, 0 < m ∧ 0 < K ∧ ∀ H : ℝ, 1 ≤ H →
      ∀ x : TracePlane, x ∈ realCutoffCorners traceBasis H →
        ENNReal.ofReal (m * Real.exp (-(K * H))) ≤ traceBoundaryTurn {x} := by
  refine ⟨traceCornerLowerConstant, 2 * traceAxisLength,
    traceCornerLowerConstant_pos, mul_pos (by norm_num) traceAxisLength_pos, ?_⟩
  intro H _ x hx
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
    (trace_real_cutoff_corner_atom_lower H x hx)

end Markov
