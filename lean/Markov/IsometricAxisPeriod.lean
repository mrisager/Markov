import Markov.HyperbolicTranslationLength

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- Every invariant isometric real line gives a lower bound on every actual
metric displacement. The period is explicit, not assumed to be a trace length. -/
theorem invariantIsometricAxis_period_le_displacement
    (g : SL(2, ℝ)) (γ : ℝ → UpperHalfPlane) (hγ : Isometry γ)
    (P : ℝ) (hP : 0 < P) (hact : ∀ t : ℝ, g • γ t = γ (t + P))
    (z : UpperHalfPlane) : P ≤ dist z (g • z) := by
  have hpow (n : ℕ) (t : ℝ) : g ^ n • γ t = γ (t + (n : ℝ) * P) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_smul, ih, hact]
      congr 1
      push_cast
      ring
  have hdist (n : ℕ) : dist z (g ^ n • z) ≤ (n : ℝ) * dist z (g • z) := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        dist z (g ^ (n+1) • z) ≤
          dist z (g ^ n • z) + dist (g ^ n • z) (g ^ (n+1) • z) := dist_triangle _ _ _
        _ = dist z (g ^ n • z) + dist z (g • z) := by rw [pow_succ, mul_smul, dist_smul]
        _ ≤ (n : ℝ) * dist z (g • z) + dist z (g • z) := by linarith [ih]
        _ = ((n+1 : ℕ) : ℝ) * dist z (g • z) := by push_cast; ring
  have hbound (n : ℕ) : (n : ℝ) * P ≤ 2 * dist (γ 0) z + (n : ℝ) * dist z (g • z) := by
    have hnP : 0 ≤ (n : ℝ) * P := mul_nonneg (Nat.cast_nonneg _) hP.le
    have he : dist (γ 0) (g ^ n • γ 0) = (n : ℝ) * P := by
      rw [hpow, hγ.dist_eq, zero_add, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hnP]
    calc
      (n : ℝ) * P = dist (γ 0) (g ^ n • γ 0) := he.symm
      _ ≤ dist (γ 0) z + dist z (g ^ n • z) + dist (g ^ n • z) (g ^ n • γ 0) :=
        (dist_triangle (γ 0) z _).trans (by linarith [dist_triangle z (g ^ n • z) (g ^ n • γ 0)])
      _ ≤ dist (γ 0) z + (n : ℝ) * dist z (g • z) + dist z (γ 0) := by
        rw [dist_smul]
        linarith [hdist n]
      _ = 2 * dist (γ 0) z + (n : ℝ) * dist z (g • z) := by rw [dist_comm z (γ 0)]; ring
  by_contra h
  have hδ : 0 < P - dist z (g • z) := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * dist (γ 0) z / (P - dist z (g • z)))
  have hn' : 2 * dist (γ 0) z < (n : ℝ) * (P - dist z (g • z)) :=
    (div_lt_iff₀ hδ).mp hn
  have hb := hbound n
  nlinarith

/-- The positive translation parameter of any actual invariant isometric line
is precisely the actual displacement infimum. No local-to-global premise is hidden. -/
theorem hyperbolicTranslationLength_eq_invariantIsometricAxis_period
    (g : SL(2, ℝ)) (γ : ℝ → UpperHalfPlane) (hγ : Isometry γ)
    (P : ℝ) (hP : 0 < P) (hact : ∀ t : ℝ, g • γ t = γ (t + P)) :
    hyperbolicTranslationLength g = P := by
  apply hyperbolicTranslationLength_eq_of_attained_lower_bound g P (γ 0)
  · exact invariantIsometricAxis_period_le_displacement g γ hγ P hP hact
  · rw [hact, zero_add, hγ.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hP]

end Markov
