import Markov.PrimitiveUnresolvedSet
import Markov.TraceUnresolvedFiniteCount
import Markov.LogarithmicCutoff

/-! The logarithmic count of v1 Lemma 7 for primitive unresolved
directions of the trace ball. The size cutoff may exceed `K` because
the unresolved predicate supplies the smaller effective cutoff. -/

noncomputable section
namespace Markov

/-- Uniform Lemma 7 for any finite set of actual primitive unresolved
directions. This version holds for every `T ≥ 1`, including `T > K`. -/
theorem trace_lemma7_finset :
    ∃ D C : ℝ, 0 < D ∧ 0 < C ∧
      ∀ (S : Finset (ℤ × ℤ)) (K H ε η T : ℝ),
        1 ≤ T → 0 < ε → 0 < η →
        (2 + ε) * η ≤ traceCornerLowerConstant *
          Real.exp (-(2 * traceAxisLength) * H) →
        D * Real.log (2 * K) ≤ H →
        (∀ d ∈ S, IsCoprime d.1 d.2) →
        (∀ d ∈ S, intEuclidean d ≤ T) →
        (∀ d ∈ S, IsTraceUnresolved d K H η) →
        (S.card : ℝ) ≤ C * (Real.log (2 * T)) ^ 2 := by
  classical
  obtain ⟨M, κ, hM, hκ, hcount⟩ := traceUnresolved_finset_card_le_coarse_cutoff
  obtain ⟨D, hD, hcutoff⟩ := exists_logarithmic_cutoff_constant
    M traceCornerLowerConstant κ (2 * traceAxisLength)
    hM traceCornerLowerConstant_pos hκ (mul_pos (by norm_num) traceAxisLength_pos)
  have hC : 0 < 72 * D ^ 2 := by positivity
  refine ⟨D, 72 * D ^ 2, hD, hC, ?_⟩
  intro S K H ε η T hT hε hη hbasic hH hprimitive hsize hunresolved
  by_cases hK : 1 ≤ K
  · let U : ℝ := min T K
    have hU : 1 ≤ U := le_min hT hK
    have hUK : U ≤ K := min_le_right T K
    have hUT : U ≤ T := min_le_left T K
    have hU0 : 0 < U := by linarith
    obtain ⟨hh, hhH, hsmall⟩ :=
      hcutoff ε K U H η hε hU hUK hη.le hbasic hH
    have hsizeU : ∀ d ∈ S, intEuclidean d ≤ U := by
      intro d hd
      exact le_min (hsize d hd) (hunresolved d hd).2.1
    have hbound := hcount S K H (D * Real.log (2 * U)) η U
      hh hhH hU hprimitive hsizeU hunresolved (by simpa only [neg_mul] using hsmall)
    have hlogU0 : 0 ≤ Real.log (2 * U) :=
      Real.log_nonneg (by linarith)
    have hlogT0 : 0 ≤ Real.log (2 * T) :=
      Real.log_nonneg (by linarith)
    have hlog : Real.log (2 * U) ≤ Real.log (2 * T) :=
      Real.log_le_log (by positivity) (by linarith)
    calc
      (S.card : ℝ) ≤ 72 * (D * Real.log (2 * U)) ^ 2 := hbound
      _ = (72 * D ^ 2) * (Real.log (2 * U)) ^ 2 := by ring
      _ ≤ (72 * D ^ 2) * (Real.log (2 * T)) ^ 2 :=
        mul_le_mul_of_nonneg_left ((sq_le_sq₀ hlogU0 hlogT0).mpr hlog) hC.le
  · have hS : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      have hun := hunresolved d hd
      exact (not_le_of_gt (lt_of_not_ge hK))
        ((intEuclidean_ge_one d hun.1).trans hun.2.1)
    rw [hS]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- The logarithmic Lemma 7 bound for the full actual finite set, without
an extra `T ≤ K` restriction. In particular it implies the paper's stated
range `1 ≤ T ≤ K`. -/
theorem trace_lemma7 :
    ∃ D C : ℝ, 0 < D ∧ 0 < C ∧
      ∀ (K H ε η T : ℝ), 1 ≤ T → 0 < ε → 0 < η →
        (2 + ε) * η ≤ traceCornerLowerConstant *
          Real.exp (-(2 * traceAxisLength) * H) →
        D * Real.log (2 * K) ≤ H →
        ((primitiveUnresolvedUpTo K H η T).card : ℝ) ≤
          C * (Real.log (2 * T)) ^ 2 := by
  obtain ⟨D, C, hD, hC, hcount⟩ := trace_lemma7_finset
  refine ⟨D, C, hD, hC, ?_⟩
  intro K H ε η T hT hε hη hbasic hH
  apply hcount (primitiveUnresolvedUpTo K H η T) K H ε η T hT hε hη hbasic hH
  · intro d hd
    exact ((mem_primitiveUnresolvedUpTo K H η T d).mp hd).1
  · intro d hd
    exact ((mem_primitiveUnresolvedUpTo K H η T d).mp hd).2.1
  · intro d hd
    exact ((mem_primitiveUnresolvedUpTo K H η T d).mp hd).2.2

/-- The same uniform bound expressed as the cardinality of the actual
primitive unresolved set, whose finiteness is proved independently. -/
theorem trace_lemma7_ncard :
    ∃ D C : ℝ, 0 < D ∧ 0 < C ∧
      ∀ (K H ε η T : ℝ), 1 ≤ T → 0 < ε → 0 < η →
        (2 + ε) * η ≤ traceCornerLowerConstant *
          Real.exp (-(2 * traceAxisLength) * H) →
        D * Real.log (2 * K) ≤ H →
        ((primitiveUnresolvedSet K H η T).ncard : ℝ) ≤
          C * (Real.log (2 * T)) ^ 2 := by
  obtain ⟨D, C, hD, hC, hcount⟩ := trace_lemma7
  refine ⟨D, C, hD, hC, ?_⟩
  intro K H ε η T hT hε hη hbasic hH
  rw [ncard_primitiveUnresolvedSet]
  exact hcount K H ε η T hT hε hη hbasic hH

end Markov
