import Markov.TraceRayLimit
import Markov.MatrixTraceRay
import Markov.SupportDerivative
import Markov.SelectedSeparation

/-! Identification of the selected supporting-functional value from the
Fricke recurrence, following the integral-ray proof in §3.1. Only the geometric
trace–length data remain assumptions; the derivative and asymptotic formula
are proved rather than assumed. -/

noncomputable section
attribute [-instance] DivisionRing.toRatAlgebra
local instance selectedTraceValueRatRealAlgebra : Algebra ℚ ℝ := DivisionRing.toRatAlgebra
open Filter
open scoped Topology

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The selected value is `2 log A₊`, provided the basis rays carry the
specified Fricke trace–length data. -/
theorem selectedSupport_value_of_ray_traces (B : Module.Basis (Fin 2) ℝ E)
    (t b c : ℤ) [ht : Fact (3 ≤ t)] (hb : 0 < b)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c)
    (htu : (t : ℝ) = 2 * Real.cosh (‖B 0‖ / 2))
    (hray : ∀ n : ℕ, (frickeRay t b c (n + 1) : ℝ) =
      2 * Real.cosh (‖((n : ℝ) + 1) • B 0 + B 1‖ / 2)) :
    selectedSupport B (B 1) = 2 * Real.log (traceRealEmbedding t (traceCoefficient t b c)) := by
  have hbase := traceLength_eq_two_log_root t ht.out ‖B 0‖ (norm_nonneg _) htu
  have hl := (frickeRay_length_limit t b c hb hf).comp (tendsto_add_atTop_nat 1)
  have hn : Tendsto
      (fun n : ℕ => ‖((n : ℝ) + 1) • B 0 + B 1‖ - ((n : ℝ) + 1) * ‖B 0‖)
      atTop (𝓝 (2 * Real.log (traceRealEmbedding t (traceCoefficient t b c)))) := by
    convert hl using 1
    ext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    rw [length_eq_two_arcosh _ _ (norm_nonneg _) (hray n), hbase]
    ring
  exact tendsto_nhds_unique (selectedSupport_integral_ray_limit B) hn

/-- Integral-direction form, ready for the paper's selected-support estimate. -/
theorem selectedSupportAt_value_of_ray_traces (B : Module.Basis (Fin 2) ℝ E)
    (t b c : ℤ) [Fact (3 ≤ t)] (hb : 0 < b)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c)
    (u v : ℤ × ℤ) (hdet : intDet u v ≠ 0)
    (htu : (t : ℝ) = 2 * Real.cosh (‖intVector B u‖ / 2))
    (hray : ∀ n : ℕ, (frickeRay t b c (n + 1) : ℝ) =
      2 * Real.cosh (‖((n : ℝ) + 1) • intVector B u + intVector B v‖ / 2)) :
    selectedSupportAt B u v (intVector B v) =
      2 * Real.log (traceRealEmbedding t (traceCoefficient t b c)) := by
  have h := selectedSupport_value_of_ray_traces (intPairBasis B u v hdet) t b c hb hf
    (by simpa only [intPairBasis_zero] using htu)
    (by simpa only [intPairBasis_zero, intPairBasis_one] using hray)
  simpa only [selectedSupportAt, dif_pos hdet, intPairBasis_one] using h

/-- The determinant separation theorem with the selected-value hypothesis
fully discharged by the Fricke-ray trace–length input. -/
theorem selectedSupport_det_lower_bound_of_ray_traces (B : Module.Basis (Fin 2) ℝ E)
    (t b c : ℤ) [Fact (3 ≤ t)] (hb : 0 < b)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c)
    (u v d : ℤ × ℤ) (A : ℝ)
    (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hv : intHeight v ≤ 2 * A)
    (hdet : |intDet u v| = 1) (hd : d ≠ (0, 0))
    (htu : (t : ℝ) = 2 * Real.cosh (‖intVector B u‖ / 2))
    (hbv : (b : ℝ) = 2 * Real.cosh (‖intVector B v‖ / 2))
    (hray : ∀ n : ℕ, (frickeRay t b c (n + 1) : ℝ) =
      2 * Real.cosh (‖((n : ℝ) + 1) • intVector B u + intVector B v‖ / 2)) :
    Real.exp (-(planeSeparationConstant B * intEuclidean d * A ^ 2)) ≤
      |integralCovectorDet (dualCoordinates B (selectedSupportAt B u v)) d| := by
  have hdet0 : intDet u v ≠ 0 := by
    intro h
    rw [h, abs_zero] at hdet
    norm_num at hdet
  exact selectedSupport_det_lower_bound B t b c hb hf u v d A hA hu hv hdet hd htu hbv
    (selectedSupportAt_value_of_ray_traces B t b c hb hf u v hdet0 htu hray)

/-- Matrix form of the separation certificate. Determinant-one integral
matrices with commutator trace -2 supply the Fricke relation and ray recurrence.
Only their geometric identification with norm lengths remains an input. -/
theorem selectedSupport_det_lower_bound_of_matrix_traces
    (B : Module.Basis (Fin 2) ℝ E) (M N : Matrix (Fin 2) (Fin 2) ℤ)
    [Fact (3 ≤ M.trace)] (hb : 0 < N.trace)
    (hM : M.det = 1) (hN : N.det = 1)
    (hc : (M * N * M.adjugate * N.adjugate).trace = -2)
    (u v d : ℤ × ℤ) (A : ℝ)
    (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hv : intHeight v ≤ 2 * A)
    (hdet : |intDet u v| = 1) (hd : d ≠ (0, 0))
    (htu : (M.trace : ℝ) = 2 * Real.cosh (‖intVector B u‖ / 2))
    (hbv : (N.trace : ℝ) = 2 * Real.cosh (‖intVector B v‖ / 2))
    (hray : ∀ n : ℕ, ((M ^ (n + 1) * N).trace : ℝ) =
      2 * Real.cosh (‖((n : ℝ) + 1) • intVector B u + intVector B v‖ / 2)) :
    Real.exp (-(planeSeparationConstant B * intEuclidean d * A ^ 2)) ≤
      |integralCovectorDet (dualCoordinates B (selectedSupportAt B u v)) d| := by
  apply selectedSupport_det_lower_bound_of_ray_traces B M.trace N.trace (M * N).trace hb
    (matrix_fricke_of_commutator M N hM hN hc) u v d A hA hu hv hdet hd htu hbv
  intro n
  rw [← matrix_trace_ray_eq_frickeRay M N hM]
  exact hray n

end Markov
