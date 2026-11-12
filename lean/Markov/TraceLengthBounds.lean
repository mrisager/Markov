import Markov.SupportSeparation
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-! Trace-height estimates from the hyperbolic trace–length relation. The
lengths and their geometric interpretation are explicit inputs; the real
analysis and norm-comparison consequences are proved here. -/

noncomputable section
attribute [-instance] DivisionRing.toRatAlgebra
local instance : Algebra ℚ ℝ := DivisionRing.toRatAlgebra

namespace Markov

/-- The expanding algebraic root is the exponential of half the length. -/
theorem traceLength_eq_two_log_root (t : ℤ) (ht : 3 ≤ t) (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (htrace : (t : ℝ) = 2 * Real.cosh (ℓ / 2)) :
    ℓ = 2 * Real.log (positiveTraceRoot t) := by
  have hr : 0 < positiveTraceRoot t := by linarith [positiveTraceRoot_gt_one t ht]
  have hl : 0 ≤ Real.log (positiveTraceRoot t) :=
    Real.log_nonneg (positiveTraceRoot_gt_one t ht).le
  have heq : Real.cosh (ℓ / 2) = Real.cosh (Real.log (positiveTraceRoot t)) := by
    rw [Real.cosh_log hr, positiveTraceRoot_add_inv t ht]
    linarith
  have hhalf := Real.cosh_injOn (show ℓ / 2 ∈ Set.Ici 0 by exact div_nonneg hℓ (by norm_num))
    (show Real.log (positiveTraceRoot t) ∈ Set.Ici 0 from hl) heq
  linarith

theorem traceRoot_eq_exp_half_length (t : ℤ) (ht : 3 ≤ t) (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (htrace : (t : ℝ) = 2 * Real.cosh (ℓ / 2)) :
    positiveTraceRoot t = Real.exp (ℓ / 2) := by
  have hh : ℓ / 2 = Real.log (positiveTraceRoot t) := by
    linarith [traceLength_eq_two_log_root t ht ℓ hℓ htrace]
  rw [hh, Real.exp_log (by linarith [positiveTraceRoot_gt_one t ht])]

/-- Identify the algebraic coefficient with the real quotient in the paper. -/
theorem traceCoefficient_real_quotient (t b c : ℤ) [Fact (3 ≤ t)] :
    traceRealEmbedding t (traceCoefficient t b c) =
      ((c : ℝ) - (positiveTraceRoot t)⁻¹ * (b : ℝ)) /
        (positiveTraceRoot t - (positiveTraceRoot t)⁻¹) := by
  rw [traceCoefficient_eq, map_div₀, map_sub, map_sub, map_mul, map_inv₀,
    map_intCast, map_intCast, traceRealEmbedding_root]

theorem trace_log_le_half_length_add_one (T ℓ : ℝ) (hT : 0 < T) (hℓ : 0 ≤ ℓ)
    (htrace : T = 2 * Real.cosh (ℓ / 2)) : Real.log T ≤ ℓ / 2 + 1 := by
  have he : Real.exp (-(ℓ / 2)) ≤ Real.exp (ℓ / 2) := Real.exp_le_exp.mpr (by linarith)
  have hbound : T ≤ 2 * Real.exp (ℓ / 2) := by
    rw [htrace, Real.cosh_eq]
    linarith
  have hlog := Real.log_le_log hT hbound
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hlog
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- Equation (57)'s trace-height bounds follow from length/norm comparison. -/
theorem trace_log_height_bounds (t b : ℤ) (ht : 3 ≤ t) (hb : 0 < b)
    (u v : ℤ × ℤ) (C A ℓu ℓv : ℝ)
    (hC : 0 ≤ C) (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hv : intHeight v ≤ 2 * A)
    (hℓu : 0 ≤ ℓu) (hℓv : 0 ≤ ℓv)
    (hNu : ℓu ≤ C * intEuclidean u) (hNv : ℓv ≤ C * intEuclidean v)
    (htu : (t : ℝ) = 2 * Real.cosh (ℓu / 2))
    (hbv : (b : ℝ) = 2 * Real.cosh (ℓv / 2)) :
    Real.log (t : ℝ) ≤ (2 * C + 1) * A ∧ Real.log (b : ℝ) ≤ (2 * C + 1) * A := by
  have heU : intEuclidean u ≤ 2 * A :=
    (intEuclidean_le_two_height u).trans (mul_le_mul_of_nonneg_left hu (by norm_num))
  have heV : intEuclidean v ≤ 4 * A := by
    have h := (intEuclidean_le_two_height v).trans (mul_le_mul_of_nonneg_left hv (by norm_num))
    nlinarith
  have hnU := hNu.trans (mul_le_mul_of_nonneg_left heU hC)
  have hnV := hNv.trans (mul_le_mul_of_nonneg_left heV hC)
  have hlogU := trace_log_le_half_length_add_one t ℓu (by exact_mod_cast (show 0 < t by omega)) hℓu htu
  have hlogV := trace_log_le_half_length_add_one b ℓv (by exact_mod_cast hb) hℓv hbv
  constructor <;> nlinarith

/-- Determinant separation from geometric length data, with an explicit
constant depending only on the norm-comparison constant `C`. The selected
support value on `v` remains an explicit input, as does the trace–length relation. -/
theorem supportDet_lower_bound_of_length_data (t b c : ℤ) [ht : Fact (3 ≤ t)]
    (hb : 0 < b) (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c)
    (lam : ℝ × ℝ) (u v d : ℤ × ℤ) (C A ℓu ℓv : ℝ)
    (hC : 0 ≤ C) (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hv : intHeight v ≤ 2 * A)
    (hdet : |intDet u v| = 1) (hd : d ≠ (0, 0))
    (hℓu : 0 ≤ ℓu) (hℓv : 0 ≤ ℓv)
    (hNu : ℓu ≤ C * intEuclidean u) (hNv : ℓv ≤ C * intEuclidean v)
    (htu : (t : ℝ) = 2 * Real.cosh (ℓu / 2))
    (hbv : (b : ℝ) = 2 * Real.cosh (ℓv / 2))
    (hlamu : realCovectorEval lam u = ℓu)
    (hlamv : realCovectorEval lam v =
      2 * Real.log (traceRealEmbedding t (traceCoefficient t b c))) :
    Real.exp (-((48 * C + 25) * intEuclidean d * A ^ 2)) ≤ |integralCovectorDet lam d| := by
  have hs := trace_log_height_bounds t b ht.out hb u v C A ℓu ℓv hC hA hu hv
    hℓu hℓv hNu hNv htu hbv
  have huval := hlamu.trans (traceLength_eq_two_log_root t ht.out ℓu hℓu htu)
  have h := supportDet_lower_bound_of_trace_bounds t b c hb hf lam u v d (2 * C + 1) A
    hA hu hv hdet hd hs.1 hs.2 huval hlamv
  convert h using 1
  congr 1
  ring

theorem supportSeparationConstant_pos (C : ℝ) (hC : 0 ≤ C) : 0 < 48 * C + 25 := by linarith

end Markov
