import Markov.SizeBounds

/-! Quantitative separation for integer trace data. The exponential size
bounds are proved, rather than assumed. The final uniform version takes
the paper's trace-height and covector-height estimates as explicit inputs. -/

noncomputable section
attribute [-instance] DivisionRing.toRatAlgebra
local instance : Algebra ℚ ℝ := DivisionRing.toRatAlgebra

namespace Markov

/-- A lower bound depending only on the integer traces and exponents. -/
theorem trace_log_linear_form_explicit_lower_bound (t b c : ℤ) [ht : Fact (3 ≤ t)]
    (hb : 0 < b) (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) (m n : ℤ)
    (hexp : m ≠ 0 ∨ n ≠ 0) :
    Real.exp (-((|(m : ℝ)| + 4 * |(n : ℝ)|) * Real.log (t : ℝ) +
      |(n : ℝ)| * Real.log (b : ℝ) + 1)) ≤
      |2 * Real.log (positiveTraceRoot t) * (m : ℝ) -
        2 * Real.log (traceRealEmbedding t (traceCoefficient t b c)) * (n : ℝ)| := by
  have htt : 3 ≤ t := ht.out
  have hlogt : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ t by omega))
  have hlogb : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ b by omega))
  have h := trace_beta_log_lower_bound t b c hb hf m n hexp
    (2 * |(n : ℝ)| * Real.log (t : ℝ))
    (|(m : ℝ)| * Real.log (t : ℝ) + |(n : ℝ)| * Real.log (b : ℝ)) 1
    (by positivity) (by positivity) le_rfl
    (by simpa only [mul_one] using traceClearingFactor_exp_bound t n ht.out)
    (by simpa only [mul_one] using traceBeta_conjugate_exp_bound t b c hb hf m n)
  calc
    _ = Real.exp (-((2 * (2 * |(n : ℝ)| * Real.log (t : ℝ)) +
        (|(m : ℝ)| * Real.log (t : ℝ) + |(n : ℝ)| * Real.log (b : ℝ)) + 1) * 1)) := by
      congr 1
      ring
    _ ≤ 2 * |Real.log (traceRealEmbedding t
        (traceRoot t ^ m * traceCoefficient t b c ^ (-n)))| := h
    _ = |2 * Real.log (traceRealEmbedding t
        (traceRoot t ^ m * traceCoefficient t b c ^ (-n)))| := by rw [abs_mul]; norm_num
    _ = _ := by rw [trace_beta_log_identity t b c hb hf]; congr 1; ring

/-- Insert the height estimates from equation (57). The remaining hypotheses
are precisely size estimates and integer trace data, with no postulated
exponential norm or conjugate bounds. -/
theorem trace_log_linear_form_height_bound (t b c : ℤ) [ht : Fact (3 ≤ t)]
    (hb : 0 < b) (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) (m n : ℤ)
    (hexp : m ≠ 0 ∨ n ≠ 0) (L B A D : ℝ)
    (hB : 0 ≤ B) (hA : 1 ≤ A) (hD : 1 ≤ D)
    (htsize : Real.log (t : ℝ) ≤ L * A) (hbsize : Real.log (b : ℝ) ≤ L * A)
    (hmsize : |(m : ℝ)| ≤ B * D * A) (hnsize : |(n : ℝ)| ≤ B * D * A) :
    Real.exp (-((6 * B * L + 1) * D * A ^ 2)) ≤
      |2 * Real.log (positiveTraceRoot t) * (m : ℝ) -
        2 * Real.log (traceRealEmbedding t (traceCoefficient t b c)) * (n : ℝ)| := by
  have htt : 3 ≤ t := ht.out
  have hlogt : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ t by omega))
  have hlogb : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ b by omega))
  have hm := mul_le_mul hmsize htsize hlogt (show 0 ≤ B * D * A by positivity)
  have hn := mul_le_mul hnsize htsize hlogt (show 0 ≤ B * D * A by positivity)
  have hnb := mul_le_mul hnsize hbsize hlogb (show 0 ≤ B * D * A by positivity)
  have hA2 : 1 ≤ A ^ 2 := by nlinarith [sq_nonneg (A - 1)]
  have hE : 1 ≤ D * A ^ 2 := by
    have hm := mul_nonneg (show 0 ≤ D - 1 by linarith) (sq_nonneg A)
    nlinarith
  have hsize : (|(m : ℝ)| + 4 * |(n : ℝ)|) * Real.log (t : ℝ) +
      |(n : ℝ)| * Real.log (b : ℝ) + 1 ≤ (6 * B * L + 1) * D * A ^ 2 := by
    nlinarith only [hm, hn, hnb, hE]
  calc
    _ ≤ Real.exp (-((|(m : ℝ)| + 4 * |(n : ℝ)|) * Real.log (t : ℝ) +
        |(n : ℝ)| * Real.log (b : ℝ) + 1)) := Real.exp_le_exp.mpr (neg_le_neg hsize)
    _ ≤ _ := trace_log_linear_form_explicit_lower_bound t b c hb hf m n hexp

end Markov
