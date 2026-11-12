import Markov.SupportCoordinates

/-! The determinant version of the arithmetic estimate. The real covector
values and trace-height estimates remain explicit geometric inputs. No
McShane–Rivin supporting functional is postulated to exist by this file. -/

noncomputable section
attribute [-instance] DivisionRing.toRatAlgebra
local instance : Algebra ℚ ℝ := DivisionRing.toRatAlgebra

namespace Markov

/-- Lemma 5's determinant bound once the geometric trace formulas and trace
size bounds are available. Euclidean covector evaluation bounds are proved. -/
theorem supportDet_lower_bound_of_trace_bounds (t b c : ℤ) [Fact (3 ≤ t)]
    (hb : 0 < b) (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c)
    (lam : ℝ × ℝ) (u v d : ℤ × ℤ) (L A : ℝ)
    (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hv : intHeight v ≤ 2 * A)
    (hdet : |intDet u v| = 1) (hd : d ≠ (0, 0))
    (htsize : Real.log (t : ℝ) ≤ L * A) (hbsize : Real.log (b : ℝ) ≤ L * A)
    (hlamu : realCovectorEval lam u = 2 * Real.log (positiveTraceRoot t))
    (hlamv : realCovectorEval lam v =
      2 * Real.log (traceRealEmbedding t (traceCoefficient t b c))) :
    Real.exp (-((24 * L + 1) * intEuclidean d * A ^ 2)) ≤ |integralCovectorDet lam d| := by
  have hD := intEuclidean_ge_one d hd
  have hD0 := intEuclidean_nonneg d
  have hdet0 : intDet u v ≠ 0 := by
    intro h
    rw [h, abs_zero] at hdet
    norm_num at hdet
  have hm : |(intEval d v : ℝ)| ≤ 4 * intEuclidean d * A := by
    calc
      _ ≤ 2 * intEuclidean d * intHeight v := intEval_abs_le_euclidean_height d v
      _ ≤ 2 * intEuclidean d * (2 * A) :=
        mul_le_mul_of_nonneg_left hv (by positivity)
      _ = _ := by ring
  have hn : |(intEval d u : ℝ)| ≤ 4 * intEuclidean d * A := by
    calc
      _ ≤ 2 * intEuclidean d * intHeight u := intEval_abs_le_euclidean_height d u
      _ ≤ 2 * intEuclidean d * A := mul_le_mul_of_nonneg_left hu (by positivity)
      _ ≤ _ := by nlinarith
  have h := trace_log_linear_form_height_bound t b c hb hf (intEval d v) (intEval d u)
    (intCovector_evals_nonzero u v d hdet0 hd) L 4 A (intEuclidean d)
    (by norm_num) hA hD htsize hbsize hm hn
  have hi := covectorDet_abs_basis lam d u v hdet
  rw [hlamu, hlamv] at hi
  rw [hi]
  norm_num only [show (6 : ℝ) * 4 = 24 by norm_num] at h
  exact h

end Markov
