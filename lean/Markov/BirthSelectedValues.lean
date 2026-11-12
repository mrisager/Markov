import Markov.TraceCompatibility

/-! Exact selected support values at the birth of a seeded Farey direction.
The ray limits are supplied by the actual matrix words, with norm/trace
compatibility retained explicitly until the trace-plane specialization. -/

noncomputable section

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The selected value along an actual seeded matrix ray. -/
theorem SeededFarey.selected_value (B : Module.Basis (Fin 2) ℝ E)
    {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (hp0 : PositiveFrickePair M0 N0) (hdet0 : intDet u0 v0 ≠ 0)
    (htrace : SeededTraceLengthCompatible B u0 v0 M0 N0)
    (h : SeededFarey u0 v0 M0 N0 u v M N) [Fact (3 ≤ M.trace)] :
    selectedSupportAt B u v (intVector B v) =
      2 * Real.log (traceRealEmbedding M.trace
        (traceCoefficient M.trace N.trace (M * N).trace)) := by
  have hp := h.positiveFrickePair hp0
  apply selectedSupportAt_value_of_ray_traces B M.trace N.trace (M * N).trace
    (by linarith [hp.trace_right]) hp.fricke u v
    (by rwa [h.det_eq_seed]) (htrace h).1
  intro n
  rw [← matrix_trace_ray_eq_frickeRay M N hp.det_left]
  have hr := (htrace (h.integral_ray (n + 1))).2
  simpa only [intVector_nsmul_add, Nat.cast_add, Nat.cast_one] using hr

/-- The opposite selected value follows from the actual right matrix ray. -/
theorem SeededFarey.reversed_selected_value (B : Module.Basis (Fin 2) ℝ E)
    {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (hp0 : PositiveFrickePair M0 N0) (hdet0 : intDet u0 v0 ≠ 0)
    (htrace : SeededTraceLengthCompatible B u0 v0 M0 N0)
    (h : SeededFarey u0 v0 M0 N0 u v M N) [Fact (3 ≤ N.trace)] :
    selectedSupportAt B v u (intVector B u) =
      2 * Real.log (traceRealEmbedding N.trace
        (traceCoefficient N.trace M.trace (M * N).trace)) := by
  have hp := h.positiveFrickePair hp0
  have hf : N.trace ^ 2 + M.trace ^ 2 + (M * N).trace ^ 2 =
      N.trace * M.trace * (M * N).trace := by nlinarith [hp.fricke]
  have hd : intDet v u ≠ 0 := by
    have hh : intDet u v ≠ 0 := by rwa [h.det_eq_seed]
    dsimp [intDet] at *
    intro he
    apply hh
    nlinarith
  apply selectedSupportAt_value_of_ray_traces B N.trace M.trace (M * N).trace
    (by linarith [hp.trace_left]) hf v u hd (htrace h).2
  intro n
  have hr := (htrace (h.right_integral_ray (n + 1))).1
  have hword : ((M * N ^ (n + 1)).trace : ℝ) =
      (frickeRay N.trace M.trace (M * N).trace (n + 1) : ℝ) := by
    rw [Matrix.trace_mul_comm M (N ^ (n + 1)),
      matrix_trace_ray_eq_frickeRay N M hp.det_right, Matrix.trace_mul_comm N M]
  rw [← hword]
  rw [add_comm u ((n + 1) • v)] at hr
  simpa only [intVector_nsmul_add, Nat.cast_add, Nat.cast_one] using hr

/-- Both endpoint support values at the birth of `u + v`. The initial
coefficient on each side is the actual adjacent matrix trace, and its next
coefficient is respectively `t a - b` and `t b - a`. -/
theorem SeededFarey.birth_selected_values (B : Module.Basis (Fin 2) ℝ E)
    {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (hp0 : PositiveFrickePair M0 N0) (hdet0 : intDet u0 v0 ≠ 0)
    (htrace : SeededTraceLengthCompatible B u0 v0 M0 N0)
    (h : SeededFarey u0 v0 M0 N0 u v M N) :
    letI : Fact (3 ≤ (M * N).trace) := ⟨(h.positiveFrickePair hp0).trace_product⟩
    selectedSupportAt B (u + v) u (intVector B u) =
        2 * Real.log (traceRealEmbedding (M * N).trace
          (traceCoefficient (M * N).trace M.trace
            ((M * N).trace * M.trace - N.trace))) ∧
      selectedSupportAt B (u + v) v (intVector B v) =
        2 * Real.log (traceRealEmbedding (M * N).trace
          (traceCoefficient (M * N).trace N.trace
            ((M * N).trace * N.trace - M.trace))) := by
  have hp := h.positiveFrickePair hp0
  letI : Fact (3 ≤ (M * N).trace) := ⟨hp.trace_product⟩
  have hc1 : (M * (M * N)).trace = (M * N).trace * M.trace - N.trace := by
    rw [matrix_trace_left_move M N hp.det_left]
    ring
  have hc2 : ((M * N) * N).trace = (M * N).trace * N.trace - M.trace := by
    rw [matrix_trace_right_move M N hp.det_right]
    ring
  constructor
  · have hh := h.left.reversed_selected_value B hp0 hdet0 htrace
    rw [hc1] at hh
    exact hh
  · have hh := h.right.selected_value B hp0 hdet0 htrace
    rw [hc2] at hh
    exact hh

/-- Birth values for any of the four concrete quadrant matrix seeds. -/
theorem SeededFarey.quadrant_birth_selected_values (B : Module.Basis (Fin 2) ℝ E)
    (htrace : QuadrantTraceLengthCompatible B) (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N) :
    letI : Fact (3 ≤ (M * N).trace) :=
      ⟨(h.positiveFrickePair (quadrantSeed_positiveFrickePair k)).trace_product⟩
    selectedSupportAt B (u + v) u (intVector B u) =
        2 * Real.log (traceRealEmbedding (M * N).trace
          (traceCoefficient (M * N).trace M.trace
            ((M * N).trace * M.trace - N.trace))) ∧
      selectedSupportAt B (u + v) v (intVector B v) =
        2 * Real.log (traceRealEmbedding (M * N).trace
          (traceCoefficient (M * N).trace N.trace
            ((M * N).trace * N.trace - M.trace))) :=
  h.birth_selected_values B (quadrantSeed_positiveFrickePair k)
    (by rw [quadrantSeed_det_eq_one]; norm_num) (htrace k)

/-- The constructed trace norm supplies both birth values without any
remaining compatibility assumption. -/
theorem SeededFarey.trace_birth_selected_values (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N) :
    letI : Fact (3 ≤ (M * N).trace) :=
      ⟨(h.positiveFrickePair (quadrantSeed_positiveFrickePair k)).trace_product⟩
    selectedSupportAt traceBasis (u + v) u (intVector traceBasis u) =
        2 * Real.log (traceRealEmbedding (M * N).trace
          (traceCoefficient (M * N).trace M.trace
            ((M * N).trace * M.trace - N.trace))) ∧
      selectedSupportAt traceBasis (u + v) v (intVector traceBasis v) =
        2 * Real.log (traceRealEmbedding (M * N).trace
          (traceCoefficient (M * N).trace N.trace
            ((M * N).trace * N.trace - M.trace))) :=
  h.quadrant_birth_selected_values traceBasis tracePlane_quadrantTraceLengthCompatible k

end Markov
