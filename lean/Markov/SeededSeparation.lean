import Markov.SeededFarey
import Markov.QuadrantSeeds
import Markov.SelectedTraceValue

/-! Separation for arbitrary seeded Farey words and the four concrete
quadrant seeds. Norm/trace compatibility remains an explicit geometric
hypothesis; no such norm or torus identification is asserted here. -/

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Geometric trace–length compatibility on every word pair generated from
the specified seed. This is an explicit proposition, not an axiom. -/
def SeededTraceLengthCompatible (B : Module.Basis (Fin 2) ℝ E)
    (u0 v0 : ℤ × ℤ) (M0 N0 : IntMatrixTwo) : Prop :=
  ∀ {u v : ℤ × ℤ} {M N : IntMatrixTwo}, SeededFarey u0 v0 M0 N0 u v M N →
    (M.trace : ℝ) = 2 * Real.cosh (‖intVector B u‖ / 2) ∧
    (N.trace : ℝ) = 2 * Real.cosh (‖intVector B v‖ / 2)

/-- The full arithmetic separation argument for a seeded Farey word pair.
The trace and ray inputs are derived from the explicit compatibility property. -/
theorem SeededFarey.separation (B : Module.Basis (Fin 2) ℝ E)
    {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (hp0 : PositiveFrickePair M0 N0) (hdet0 : intDet u0 v0 = 1)
    (htrace : SeededTraceLengthCompatible B u0 v0 M0 N0)
    (h : SeededFarey u0 v0 M0 N0 u v M N)
    (d : ℤ × ℤ) (A : ℝ) (hA : 1 ≤ A) (hu : intHeight u ≤ A)
    (hv : intHeight v ≤ 2 * A) (hd : d ≠ (0, 0)) :
    Real.exp (-(planeSeparationConstant B * intEuclidean d * A ^ 2)) ≤
      |integralCovectorDet (dualCoordinates B (selectedSupportAt B u v)) d| := by
  have hp := h.positiveFrickePair hp0
  letI : Fact (3 ≤ M.trace) := ⟨hp.trace_left⟩
  apply selectedSupport_det_lower_bound_of_matrix_traces B M N
    (by linarith [hp.trace_right]) hp.det_left hp.det_right (h.commutator_trace hp0)
    u v d A hA hu hv (by rw [h.det_eq_seed, hdet0]; norm_num) hd (htrace h).1 (htrace h).2
  intro n
  have hr := (htrace (h.integral_ray (n + 1))).2
  simpa only [intVector_nsmul_add, Nat.cast_add, Nat.cast_one] using hr

/-- The norm–trace compatibility property in all four quadrant
markings. `TraceSeparation` proves the constructed-norm instance. -/
def QuadrantTraceLengthCompatible (B : Module.Basis (Fin 2) ℝ E) : Prop :=
  ∀ k : Fin 4, SeededTraceLengthCompatible B
    (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
    (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2

/-- Every word witness in any concrete quadrant satisfies the separation
bound, relative to the stated geometric compatibility. -/
theorem SeededFarey.quadrant_separation (B : Module.Basis (Fin 2) ℝ E)
    (htrace : QuadrantTraceLengthCompatible B) (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N)
    (d : ℤ × ℤ) (A : ℝ) (hA : 1 ≤ A) (hu : intHeight u ≤ A)
    (hv : intHeight v ≤ 2 * A) (hd : d ≠ (0, 0)) :
    Real.exp (-(planeSeparationConstant B * intEuclidean d * A ^ 2)) ≤
      |integralCovectorDet (dualCoordinates B (selectedSupportAt B u v)) d| :=
  h.separation B (quadrantSeed_positiveFrickePair k) (quadrantSeed_det_eq_one k)
    (htrace k) d A hA hu hv hd

/-- Separation with the two labels reversed. The determinant is -1 and the
right integral ray supplies the selected support value in the other order. -/
theorem SeededFarey.reversed_separation (B : Module.Basis (Fin 2) ℝ E)
    {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (hp0 : PositiveFrickePair M0 N0) (hdet0 : intDet u0 v0 = 1)
    (htrace : SeededTraceLengthCompatible B u0 v0 M0 N0)
    (h : SeededFarey u0 v0 M0 N0 u v M N)
    (d : ℤ × ℤ) (A : ℝ) (hA : 1 ≤ A) (hv : intHeight v ≤ A)
    (hu : intHeight u ≤ 2 * A) (hd : d ≠ (0, 0)) :
    Real.exp (-(planeSeparationConstant B * intEuclidean d * A ^ 2)) ≤
      |integralCovectorDet (dualCoordinates B (selectedSupportAt B v u)) d| := by
  have hp := h.positiveFrickePair hp0
  letI : Fact (3 ≤ N.trace) := ⟨hp.trace_right⟩
  have hfricke : N.trace ^ 2 + M.trace ^ 2 + (M * N).trace ^ 2 =
      N.trace * M.trace * (M * N).trace := by nlinarith [hp.fricke]
  have hdet : intDet v u = -1 := by
    have hh := h.det_eq_seed.trans hdet0
    dsimp [intDet] at *
    nlinarith
  apply selectedSupport_det_lower_bound_of_ray_traces B N.trace M.trace (M * N).trace
    (by linarith [hp.trace_left]) hfricke v u d A hA hv hu
    (by rw [hdet]; norm_num) hd (htrace h).2 (htrace h).1
  intro n
  have hr := (htrace (h.right_integral_ray (n + 1))).1
  have hword : ((M * N ^ (n + 1)).trace : ℝ) =
      (frickeRay N.trace M.trace (M * N).trace (n + 1) : ℝ) := by
    rw [Matrix.trace_mul_comm M (N ^ (n + 1)),
      matrix_trace_ray_eq_frickeRay N M hp.det_right, Matrix.trace_mul_comm N M]
  rw [← hword]
  rw [add_comm u ((n + 1) • v)] at hr
  simpa only [intVector_nsmul_add, Nat.cast_add, Nat.cast_one] using hr

/-- Reversed-label separation for any word witness in any concrete quadrant. -/
theorem SeededFarey.quadrant_reversed_separation (B : Module.Basis (Fin 2) ℝ E)
    (htrace : QuadrantTraceLengthCompatible B) (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N)
    (d : ℤ × ℤ) (A : ℝ) (hA : 1 ≤ A) (hv : intHeight v ≤ A)
    (hu : intHeight u ≤ 2 * A) (hd : d ≠ (0, 0)) :
    Real.exp (-(planeSeparationConstant B * intEuclidean d * A ^ 2)) ≤
      |integralCovectorDet (dualCoordinates B (selectedSupportAt B v u)) d| :=
  h.reversed_separation B (quadrantSeed_positiveFrickePair k) (quadrantSeed_det_eq_one k)
    (htrace k) d A hA hv hu hd

end Markov
