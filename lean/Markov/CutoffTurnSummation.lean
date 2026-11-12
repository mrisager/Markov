import Markov.GlobalCutoffCoverage
import Markov.CutoffGapCount
import Markov.TraceBoundaryTurn
import Mathlib.MeasureTheory.Measure.Real

/-! Finite summation of explicit bounds for the actual signed cutoff arcs.
The analytic bound on each gap is an input; the coverage and arithmetic
count convert it into a bound on the entire uncut trace boundary. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual boundary complement is covered by the finite signed family
indexed by consecutive arithmetic cutoff pairs. -/
theorem uncut_boundary_subset_iUnion_signedGapIndices
    (B : Module.Basis (Fin 2) ℝ E) (H : ℕ) (hH : 1 ≤ H) :
    frontier (Metric.closedBall (0 : E) 1) \ (↑(cutoffCorners B H) : Set E) ⊆
      ⋃ i ∈ signedGapIndices H,
        slopeBoundaryArc (signedSectorBasis B i.1)
          (cutoffSlope i.2.1) (cutoffSlope i.2.2) := by
  intro x hx
  obtain ⟨k, u, v, huv, hxarc, _⟩ :=
    uncut_boundary_exists_signed_cutoff_component B H hH x hx
  exact mem_iUnion.mpr ⟨(k, (u, v)), mem_iUnion.mpr
    ⟨(mem_signedGapIndices H k u v).mpr huv, hxarc⟩⟩

/-- The signed gap index count is at most `72 H²` for a positive cutoff. -/
theorem signedGapIndices_card_le_mul_sq (H : ℕ) (hH : 1 ≤ H) :
    (signedGapIndices H).card ≤ 72 * H ^ 2 := by
  calc
    _ ≤ 8 * (2 * H + 1) ^ 2 := signedGapIndices_card_le H
    _ ≤ 8 * (3 * H) ^ 2 := by gcongr; omega
    _ = 72 * H ^ 2 := by ring

/-- Finite subadditivity bounds the actual uncut turn by the sum of the
actual signed gap turns. Overlapping arcs cause no problem. -/
theorem traceBoundaryTurn_uncut_le_sum_signedGapIndices (H : ℕ) (hH : 1 ≤ H) :
    (traceBoundaryTurn
      (frontier (Metric.closedBall (0 : TracePlane) 1) \
        (↑(cutoffCorners traceBasis H) : Set TracePlane))).toReal ≤
      ∑ i ∈ signedGapIndices H,
        (traceBoundaryTurn (slopeBoundaryArc (signedSectorBasis traceBasis i.1)
          (cutoffSlope i.2.1) (cutoffSlope i.2.2))).toReal := by
  exact (measureReal_mono
    (uncut_boundary_subset_iUnion_signedGapIndices traceBasis H hH)
    (measure_ne_top traceBoundaryTurn _)).trans
    (measureReal_biUnion_finset_le (signedGapIndices H) (fun i =>
      slopeBoundaryArc (signedSectorBasis traceBasis i.1)
        (cutoffSlope i.2.1) (cutoffSlope i.2.2)))

/-- A common bound for each actual cutoff gap can be multiplied by the
finite arithmetic index count. -/
theorem traceBoundaryTurn_uncut_le_card_mul_of_gap_bound
    (H : ℕ) (hH : 1 ≤ H) (K : ℝ)
    (hgap : ∀ (k : Fin 8) (u v : ℤ × ℤ), ConsecutiveCutoffSlopes H u v →
      (traceBoundaryTurn (slopeBoundaryArc (signedSectorBasis traceBasis k)
        (cutoffSlope u) (cutoffSlope v))).toReal ≤ K) :
    (traceBoundaryTurn
      (frontier (Metric.closedBall (0 : TracePlane) 1) \
        (↑(cutoffCorners traceBasis H) : Set TracePlane))).toReal ≤
      ((signedGapIndices H).card : ℝ) * K := by
  classical
  apply (traceBoundaryTurn_uncut_le_sum_signedGapIndices H hH).trans
  calc
    _ ≤ ∑ _i ∈ signedGapIndices H, K := by
      apply Finset.sum_le_sum
      intro i hi
      exact hgap i.1 i.2.1 i.2.2 ((mem_signedGapIndices H i.1 i.2.1 i.2.2).mp hi)
    _ = ((signedGapIndices H).card : ℝ) * K := by simp

/-- A nonnegative common gap bound yields a quadratic global multiplier. -/
theorem traceBoundaryTurn_uncut_le_mul_sq_of_gap_bound
    (H : ℕ) (hH : 1 ≤ H) (K : ℝ) (hK : 0 ≤ K)
    (hgap : ∀ (k : Fin 8) (u v : ℤ × ℤ), ConsecutiveCutoffSlopes H u v →
      (traceBoundaryTurn (slopeBoundaryArc (signedSectorBasis traceBasis k)
        (cutoffSlope u) (cutoffSlope v))).toReal ≤ K) :
    (traceBoundaryTurn
      (frontier (Metric.closedBall (0 : TracePlane) 1) \
        (↑(cutoffCorners traceBasis H) : Set TracePlane))).toReal ≤
      72 * (H : ℝ) ^ 2 * K := by
  have hcard : ((signedGapIndices H).card : ℝ) ≤ 72 * (H : ℝ) ^ 2 := by
    exact_mod_cast signedGapIndices_card_le_mul_sq H hH
  exact (traceBoundaryTurn_uncut_le_card_mul_of_gap_bound H hH K hgap).trans
    (mul_le_mul_of_nonneg_right hcard hK)

/-- Explicit per-gap exponential decay gives the cubic global cutoff bound.
The analytic per-gap estimate is a hypothesis, not an added axiom. -/
theorem traceBoundaryTurn_uncut_le_exp_of_gap_bound
    (H : ℕ) (hH : 1 ≤ H) (D c : ℝ) (hD : 0 ≤ D)
    (hgap : ∀ (k : Fin 8) (u v : ℤ × ℤ), ConsecutiveCutoffSlopes H u v →
      (traceBoundaryTurn (slopeBoundaryArc (signedSectorBasis traceBasis k)
        (cutoffSlope u) (cutoffSlope v))).toReal ≤
          D * (H : ℝ) * Real.exp (-c * (H : ℝ))) :
    (traceBoundaryTurn
      (frontier (Metric.closedBall (0 : TracePlane) 1) \
        (↑(cutoffCorners traceBasis H) : Set TracePlane))).toReal ≤
      72 * D * (H : ℝ) ^ 3 * Real.exp (-c * (H : ℝ)) := by
  have hK : 0 ≤ D * (H : ℝ) * Real.exp (-c * (H : ℝ)) :=
    mul_nonneg (mul_nonneg hD (Nat.cast_nonneg H)) (Real.exp_pos _).le
  convert traceBoundaryTurn_uncut_le_mul_sq_of_gap_bound H hH _ hK hgap using 1
  ring

end Markov
