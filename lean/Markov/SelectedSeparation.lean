import Markov.NormedPlane

/-! The Lemma 5 estimate for the constructed selected supporting functional.
Only the geometric trace data, including the selected value on the second
basis direction, remain inputs. No trace-height or norm-comparison bound is
assumed: both are derived for the fixed coordinate basis. -/

noncomputable section
attribute [-instance] DivisionRing.toRatAlgebra
local instance : Algebra ℚ ℝ := DivisionRing.toRatAlgebra

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def planeSeparationConstant (B : Module.Basis (Fin 2) ℝ E) : ℝ :=
  48 * (‖B 0‖ + ‖B 1‖) + 25

theorem planeSeparationConstant_pos (B : Module.Basis (Fin 2) ℝ E) :
    0 < planeSeparationConstant B := by
  dsimp [planeSeparationConstant]
  positivity

/-- A supporting-normal separation certificate for any real normed plane
carrying the paper's integer Fricke traces and selected trace-value formula.
Instantiating these geometric trace hypotheses for the modular torus is open. -/
theorem selectedSupport_det_lower_bound (B : Module.Basis (Fin 2) ℝ E)
    (t b c : ℤ) [Fact (3 ≤ t)] (hb : 0 < b)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c)
    (u v d : ℤ × ℤ) (A : ℝ)
    (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hv : intHeight v ≤ 2 * A)
    (hdet : |intDet u v| = 1) (hd : d ≠ (0, 0))
    (htu : (t : ℝ) = 2 * Real.cosh (‖intVector B u‖ / 2))
    (hbv : (b : ℝ) = 2 * Real.cosh (‖intVector B v‖ / 2))
    (hselected : selectedSupportAt B u v (intVector B v) =
      2 * Real.log (traceRealEmbedding t (traceCoefficient t b c))) :
    Real.exp (-(planeSeparationConstant B * intEuclidean d * A ^ 2)) ≤
      |integralCovectorDet (dualCoordinates B (selectedSupportAt B u v)) d| := by
  have hdet0 : intDet u v ≠ 0 := by
    intro h
    rw [h, abs_zero] at hdet
    norm_num at hdet
  apply supportDet_lower_bound_of_length_data t b c hb hf
    (dualCoordinates B (selectedSupportAt B u v)) u v d
    (‖B 0‖ + ‖B 1‖) A ‖intVector B u‖ ‖intVector B v‖
    (by positivity) hA hu hv hdet hd
    (norm_nonneg _) (norm_nonneg _)
    (intVector_norm_le B u) (intVector_norm_le B v) htu hbv
  · rw [dualCoordinates_eval]
    exact selectedSupportAt_value_self B u v hdet0
  · simpa only [dualCoordinates_eval] using hselected

end Markov
