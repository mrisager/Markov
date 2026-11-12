import Markov.TraceIndicatorFourierDecay
import Markov.TraceRadialPoisson
import Markov.TracePoisson
import Markov.LatticePowerTail

/-! The quantitative actual Fourier tail: inverse-frequency indicator decay,
cubic Schwartz decay of the actual radial kernel, and the full lattice
fourth-power tail are combined without a conditional decay hypothesis. -/

noncomputable section
open MeasureTheory FourierTransform
namespace Markov

theorem exists_trace_mollifier_fourier_decay_three :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ : EuclideanSpace ℝ (Fin 2), ξ ≠ 0 →
      ‖𝓕 traceComplexMollifier ξ‖ ≤ A / ‖ξ‖ ^ (3 : ℕ) := by
  let f := traceScaledMollifierSchwartz 1 (by norm_num : (0 : ℝ) < 1)
  have heq : (f : EuclideanSpace ℝ (Fin 2) → ℂ) = traceComplexMollifier := by
    funext x
    change (traceScaledMollifier 1 x : ℂ) = traceComplexMollifier x
    simp only [traceScaledMollifier, one_pow, one_smul, one_mul, traceComplexMollifier]
  let A := (SchwartzMap.seminorm ℂ 3 0) (𝓕 f)
  refine ⟨A, apply_nonneg _ _, ?_⟩
  intro ξ hξ
  have hh := SchwartzMap.norm_pow_mul_le_seminorm ℂ (𝓕 f) 3 ξ
  change ‖ξ‖ ^ 3 * ‖𝓕 (f : EuclideanSpace ℝ (Fin 2) → ℂ) ξ‖ ≤ A at hh
  rw [heq] at hh
  apply (le_div_iff₀ (pow_pos (norm_pos_iff.mpr hξ) 3)).mpr
  simpa only [mul_comm] using hh

theorem trace_fourier_lattice_term_decay_four
    (C A : ℝ) (hC : 0 ≤ C)
    (hχ : ∀ ξ : EuclideanSpace ℝ (Fin 2), ξ ≠ 0 →
      ‖𝓕 (traceComplexBallIndicator 1) ξ‖ ≤ C / ‖ξ‖)
    (hρ : ∀ ξ : EuclideanSpace ℝ (Fin 2), ξ ≠ 0 →
      ‖𝓕 traceComplexMollifier ξ‖ ≤ A / ‖ξ‖ ^ (3 : ℕ))
    (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q) (n : ℤ × ℤ) (hn : n ≠ 0) :
    ‖traceFourierLatticeTerm S Q n‖ ≤
      (C * A) * S * Q ^ (3 : ℕ) * (1 / intEuclidean n ^ (4 : ℕ)) := by
  have hv : euclideanIntDirection n ≠ 0 := euclideanIntDirection_ne_zero n hn
  have hr : 0 < intEuclidean n := by rw [← euclideanIntDirection_norm]; exact norm_pos_iff.mpr hv
  have hχ' : ‖𝓕 (traceComplexBallIndicator 1) (S • euclideanIntDirection n)‖ ≤
      C / (S * intEuclidean n) := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hS, euclideanIntDirection_norm] using
      hχ (S • euclideanIntDirection n) (smul_ne_zero hS.ne' hv)
  have hρ' : ‖𝓕 traceComplexMollifier (Q⁻¹ • euclideanIntDirection n)‖ ≤
      A / (Q⁻¹ * intEuclidean n) ^ (3 : ℕ) := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hQ), euclideanIntDirection_norm] using
      hρ (Q⁻¹ • euclideanIntDirection n) (smul_ne_zero (inv_ne_zero hQ.ne') hv)
  rw [traceFourierLatticeTerm, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg S)]
  calc
    _ ≤ S ^ 2 * (C / (S * intEuclidean n)) *
        (A / (Q⁻¹ * intEuclidean n) ^ (3 : ℕ)) := by gcongr
    _ = _ := by field_simp

/-- The actual full nonzero-frequency tail has order `S Q³/K²`.
All analytic and lattice decay inputs are proved for the constructed body. -/
theorem trace_fourier_tail_bound :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ S Q K : ℝ, 0 < S → 0 < Q → 1 ≤ K →
      (∑' n : ℤ × ℤ, if K < intEuclidean n then
        ‖traceFourierLatticeTerm S Q n‖ else 0) ≤
      Ctail * S * Q ^ (3 : ℕ) / K ^ (2 : ℕ) := by
  classical
  obtain ⟨C, hC, hχ⟩ := exists_trace_indicator_fourier_decay_constant
  obtain ⟨A, hA, hρ⟩ := exists_trace_mollifier_fourier_decay_three
  refine ⟨50 * C * A + 1, by positivity, ?_⟩
  intro S Q K hS hQ hK
  let F := (C * A) * S * Q ^ (3 : ℕ)
  have hF : 0 ≤ F := by positivity
  have hpoint (n : ℤ × ℤ) :
      (if K < intEuclidean n then ‖traceFourierLatticeTerm S Q n‖ else 0) ≤
        F * (if K < intEuclidean n then 1 / intEuclidean n ^ (4 : ℕ) else 0) := by
    by_cases hnK : K < intEuclidean n
    · have hn : n ≠ 0 := by
        intro hz
        subst n
        have hz : intEuclidean (0 : ℤ × ℤ) = 0 := by simp [intEuclidean]
        rw [hz] at hnK
        linarith
      simpa only [if_pos hnK, F] using
        trace_fourier_lattice_term_decay_four C A hC hχ hρ S Q hS hQ n hn
    · simp only [if_neg hnK, mul_zero, le_refl]
  have hmajor := (integer_fourth_power_tail_summable K hK).mul_left F
  have hactual : Summable (fun n : ℤ × ℤ => if K < intEuclidean n then
      ‖traceFourierLatticeTerm S Q n‖ else 0) :=
    hmajor.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hpoint
  calc
    _ ≤ ∑' n : ℤ × ℤ, F * (if K < intEuclidean n then
        1 / intEuclidean n ^ (4 : ℕ) else 0) := hactual.tsum_le_tsum hpoint hmajor
    _ = F * (∑' n : ℤ × ℤ, if K < intEuclidean n then
        1 / intEuclidean n ^ (4 : ℕ) else 0) := tsum_mul_left
    _ ≤ F * (50 / K ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left (integer_fourth_power_tail_le K hK) hF
    _ = (50 * C * A) * S * Q ^ (3 : ℕ) / K ^ (2 : ℕ) := by dsimp [F]; ring
    _ ≤ _ := by gcongr; linarith

end Markov
