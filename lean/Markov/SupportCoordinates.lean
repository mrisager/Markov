import Markov.ArithmeticSeparation
import Mathlib.Data.Real.Sqrt

/-! Coordinate estimates used in §3.1 and Lemma 5. `intEuclidean` is the
actual Euclidean length, not the product-space maximum norm. -/

noncomputable section

namespace Markov

def intHeight (u : ℤ × ℤ) : ℝ := max |(u.1 : ℝ)| |(u.2 : ℝ)|

def intEuclidean (u : ℤ × ℤ) : ℝ := Real.sqrt ((u.1 : ℝ) ^ 2 + (u.2 : ℝ) ^ 2)

theorem intHeight_nonneg (u : ℤ × ℤ) : 0 ≤ intHeight u :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem intEuclidean_nonneg (u : ℤ × ℤ) : 0 ≤ intEuclidean u := Real.sqrt_nonneg _

theorem intEuclidean_coordinate_bounds (u : ℤ × ℤ) :
    |(u.1 : ℝ)| ≤ intEuclidean u ∧ |(u.2 : ℝ)| ≤ intEuclidean u := by
  constructor <;> apply Real.abs_le_sqrt <;> nlinarith [sq_nonneg (u.1 : ℝ), sq_nonneg (u.2 : ℝ)]

theorem intEuclidean_ge_one (u : ℤ × ℤ) (hu : u ≠ (0, 0)) : 1 ≤ intEuclidean u := by
  have hc := intEuclidean_coordinate_bounds u
  by_cases h₁ : u.1 = 0
  · have h₂ : u.2 ≠ 0 := by
      intro h
      exact hu (Prod.ext h₁ h)
    have h : (1 : ℝ) ≤ |(u.2 : ℝ)| := by exact_mod_cast Int.one_le_abs h₂
    exact h.trans hc.2
  · have h : (1 : ℝ) ≤ |(u.1 : ℝ)| := by exact_mod_cast Int.one_le_abs h₁
    exact h.trans hc.1

theorem intEuclidean_le_two_height (u : ℤ × ℤ) : intEuclidean u ≤ 2 * intHeight u := by
  have hH := intHeight_nonneg u
  have h₁ : |(u.1 : ℝ)| ≤ intHeight u := le_max_left _ _
  have h₂ : |(u.2 : ℝ)| ≤ intHeight u := le_max_right _ _
  have hs₁ := (sq_le_sq₀ (abs_nonneg (u.1 : ℝ)) hH).mpr h₁
  have hs₂ := (sq_le_sq₀ (abs_nonneg (u.2 : ℝ)) hH).mpr h₂
  have hs := Real.sq_sqrt (show 0 ≤ (u.1 : ℝ) ^ 2 + (u.2 : ℝ) ^ 2 by positivity)
  have he := intEuclidean_nonneg u
  dsimp [intEuclidean] at he ⊢
  nlinarith [sq_abs (u.1 : ℝ), sq_abs (u.2 : ℝ)]

/-- The elementary evaluation bound needed in equation (57). -/
theorem intEval_abs_le_euclidean_height (d u : ℤ × ℤ) :
    |(intEval d u : ℝ)| ≤ 2 * intEuclidean d * intHeight u := by
  have hc := intEuclidean_coordinate_bounds d
  have h₁ : |(u.1 : ℝ)| ≤ intHeight u := le_max_left _ _
  have h₂ : |(u.2 : ℝ)| ≤ intHeight u := le_max_right _ _
  dsimp [intEval]
  push_cast
  calc
    |(d.1 : ℝ) * u.1 + (d.2 : ℝ) * u.2| ≤
        |(d.1 : ℝ) * u.1| + |(d.2 : ℝ) * u.2| := abs_add_le _ _
    _ ≤ intEuclidean d * intHeight u + intEuclidean d * intHeight u := by
      rw [abs_mul, abs_mul]
      exact add_le_add
        (mul_le_mul hc.1 h₁ (abs_nonneg _) (intEuclidean_nonneg d))
        (mul_le_mul hc.2 h₂ (abs_nonneg _) (intEuclidean_nonneg d))
    _ = _ := by ring

def realCovectorEval (lam : ℝ × ℝ) (u : ℤ × ℤ) : ℝ := lam.1 * u.1 + lam.2 * u.2

def integralCovectorDet (lam : ℝ × ℝ) (d : ℤ × ℤ) : ℝ := lam.1 * d.2 - lam.2 * d.1

/-- Equation (30): evaluating the two covectors on an integral basis. -/
theorem covectorDet_basis_identity (lam : ℝ × ℝ) (d u v : ℤ × ℤ) :
    integralCovectorDet lam d * (intDet u v : ℝ) =
      realCovectorEval lam u * (intEval d v : ℝ) -
        realCovectorEval lam v * (intEval d u : ℝ) := by
  dsimp [integralCovectorDet, intDet, realCovectorEval, intEval]
  push_cast
  ring

theorem covectorDet_abs_basis (lam : ℝ × ℝ) (d u v : ℤ × ℤ) (hdet : |intDet u v| = 1) :
    |integralCovectorDet lam d| =
      |realCovectorEval lam u * (intEval d v : ℝ) -
        realCovectorEval lam v * (intEval d u : ℝ)| := by
  have h := congrArg abs (covectorDet_basis_identity lam d u v)
  have hdet' : |(intDet u v : ℝ)| = 1 := by exact_mod_cast hdet
  simpa only [abs_mul, hdet', mul_one] using h

end Markov
