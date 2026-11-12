import Markov.Denominator
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential

/-! The real-analytic end of Lemma 5. The bounds on the clearing factor and
the conjugate remain explicit inputs; the geometric height estimates that
produce uniform constants are not asserted by this module. -/

noncomputable section
attribute [-instance] DivisionRing.toRatAlgebra
local instance : Algebra ℚ ℝ := DivisionRing.toRatAlgebra

namespace Markov

theorem gap_lower_bound_of_norm_bound (D β γ C₁ C₂ E : ℝ)
    (hD0 : 0 ≤ D) (hD : D ≤ Real.exp (C₁ * E))
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ Real.exp (C₂ * E)) (hC₂ : 0 ≤ C₂ * E)
    (hnorm : 1 ≤ D ^ 2 * |β - 1| * |γ - 1|) :
    (1 / 2 : ℝ) * Real.exp (-((2 * C₁ + C₂) * E)) ≤ |β - 1| := by
  have hγabs : |γ - 1| ≤ 2 * Real.exp (C₂ * E) := by
    calc
      |γ - 1| ≤ |γ| + |(1 : ℝ)| := abs_sub γ 1
      _ = γ + 1 := by rw [abs_of_nonneg hγ0, abs_one]
      _ ≤ 2 * Real.exp (C₂ * E) := by linarith [Real.one_le_exp hC₂]
  have hDsq : D ^ 2 ≤ Real.exp (C₁ * E) ^ 2 :=
    (sq_le_sq₀ hD0 (Real.exp_pos _).le).mpr hD
  have hn : 1 ≤ 2 * Real.exp ((2 * C₁ + C₂) * E) * |β - 1| := by
    calc
      1 ≤ D ^ 2 * |β - 1| * |γ - 1| := hnorm
      _ ≤ Real.exp (C₁ * E) ^ 2 * |β - 1| * (2 * Real.exp (C₂ * E)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hDsq (abs_nonneg _)) hγabs
          (abs_nonneg _) (mul_nonneg (sq_nonneg _) (abs_nonneg _))
      _ = 2 * (Real.exp (C₁ * E) * Real.exp (C₁ * E) * Real.exp (C₂ * E)) *
          |β - 1| := by ring
      _ = 2 * Real.exp ((2 * C₁ + C₂) * E) * |β - 1| := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
  calc
    (1 / 2 : ℝ) * Real.exp (-((2 * C₁ + C₂) * E)) =
        1 / (2 * Real.exp ((2 * C₁ + C₂) * E)) := by
      simp only [Real.exp_neg, one_div, mul_inv_rev]
      ring
    _ ≤ |β - 1| := (div_le_iff₀ (by positivity)).mpr (by nlinarith [hn])

theorem log_lower_bound_of_gap_bound (β C E : ℝ) (hβ : 0 < β)
    (hC : 0 ≤ C) (hE : 1 ≤ E)
    (hgap : (1 / 2 : ℝ) * Real.exp (-(C * E)) ≤ |β - 1|) :
    Real.exp (-((C + 1) * E)) ≤ 2 * |Real.log β| := by
  have htwo : (2 : ℝ) ≤ Real.exp E := by linarith [Real.add_one_le_exp E]
  have hdecay : Real.exp (-E) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) htwo
  have hsmall : Real.exp (-((C + 1) * E)) ≤ (1 / 2 : ℝ) * Real.exp (-(C * E)) := by
    calc
      Real.exp (-((C + 1) * E)) = Real.exp (-(C * E)) * Real.exp (-E) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(C * E)) * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hdecay (Real.exp_pos _).le
      _ = (1 / 2 : ℝ) * Real.exp (-(C * E)) := by ring
  by_cases hlog : |Real.log β| ≤ 1
  · have hlocal := Real.abs_exp_sub_one_le hlog
    rw [Real.exp_log hβ] at hlocal
    exact hsmall.trans (hgap.trans hlocal)
  · have hunit : Real.exp (-((C + 1) * E)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    linarith

/-- The quantitative core of v1 Lemma 5 for trace-field elements,
parametrized by the uniform exponential size bounds. -/
theorem trace_beta_log_lower_bound (t b c : ℤ) [ht : Fact (3 ≤ t)]
    (hb : 0 < b) (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c)
    (m n : ℤ) (hexp : m ≠ 0 ∨ n ≠ 0) (C₁ C₂ E : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hE : 1 ≤ E)
    (hD : (traceClearingFactor t n : ℝ) ≤ Real.exp (C₁ * E))
    (hconj : traceRealEmbedding t
      (star (traceRoot t ^ m * traceCoefficient t b c ^ (-n))) ≤ Real.exp (C₂ * E)) :
    Real.exp (-((2 * C₁ + C₂ + 1) * E)) ≤
      2 * |Real.log (traceRealEmbedding t
        (traceRoot t ^ m * traceCoefficient t b c ^ (-n)))| := by
  let β := traceRoot t ^ m * traceCoefficient t b c ^ (-n)
  have hcoeff := traceCoefficient_real_pos t b c hb hf
  have hr := positiveTraceRoot_gt_one t ht.out
  have hβ : 0 < traceRealEmbedding t β := by
    dsimp [β]
    rw [map_mul, map_zpow₀, map_zpow₀, traceRealEmbedding_root]
    exact mul_pos (zpow_pos (by linarith) _) (zpow_pos hcoeff.1 _)
  have hγ : 0 < traceRealEmbedding t (star β) := by
    dsimp [β]
    rw [star_mul, star_zpow₀, star_zpow₀, map_mul, map_zpow₀, map_zpow₀,
      traceRoot_star_eq_inv, map_inv₀, traceRealEmbedding_root]
    exact mul_pos (zpow_pos hcoeff.2 _) (zpow_pos (by positivity) _)
  have hnorm := cleared_beta_norm_lower_bound t b c hf m n hexp
  have hgap := gap_lower_bound_of_norm_bound
    (traceClearingFactor t n) (traceRealEmbedding t β) (traceRealEmbedding t (star β))
    C₁ C₂ E (by exact_mod_cast (traceClearingFactor_pos t n ht.out).le) hD
    hγ.le hconj (mul_nonneg hC₂ (by linarith)) hnorm
  exact log_lower_bound_of_gap_bound _ _ E hβ (by positivity) hE hgap

end Markov
