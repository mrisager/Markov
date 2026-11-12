import Markov.NormalHalfPlane

/-! A common open dual half-plane over the whole chord between equal-length
rays, and over their nonnegative affine cone. Positive radial rescaling and
exchanging the two rays extend the existing bounded-slope half-plane theorem.
This uses the original norm throughout. -/

noncomputable section

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive radial scaling does not change the actual norming fibre. -/
theorem normingFunctionals_pos_smul_eq (a : E) (c : ℝ) (hc : 0 < c) :
    normingFunctionals (c • a) = normingFunctionals a := by
  ext f
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    have heq := hf.2
    simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc,
      smul_eq_mul] at heq
    exact mul_left_cancel₀ hc.ne' heq
  · intro hf
    refine ⟨hf.1, ?_⟩
    simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc,
      smul_eq_mul, hf.2]

/-- The positive-sum half-plane contains every support at every nonnegative
slope, without restricting the slope to at most one. -/
theorem normingFunctional_sum_pos_of_equal_norm_nonneg
    (a b : E) (L t : ℝ) (ha : ‖a‖ = L) (hb : ‖b‖ = L)
    (hdiff : ‖a - b‖ < 2 * L) (ht : 0 ≤ t)
    (f : StrongDual ℝ E) (hf : f ∈ normingFunctionals (a + t • b)) :
    0 < f (a + b) := by
  by_cases ht1 : t ≤ 1
  · exact normingFunctional_sum_pos_of_equal_norm_Icc a b L t ha hb hdiff
      ⟨ht, ht1⟩ f hf
  · have htpos : 0 < t := by linarith
    have hline : t • (b + t⁻¹ • a) = a + t • b := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ htpos.ne', one_smul, add_comm]
    have hf' : f ∈ normingFunctionals (b + t⁻¹ • a) := by
      rw [← normingFunctionals_pos_smul_eq (b + t⁻¹ • a) t htpos, hline]
      exact hf
    have hdiff' : ‖b - a‖ < 2 * L := by
      rw [norm_sub_rev]
      exact hdiff
    have h := normingFunctional_sum_pos_of_equal_norm_Icc b a L t⁻¹ hb ha hdiff'
      ⟨inv_nonneg.mpr ht, inv_le_one_of_one_le₀ (by linarith)⟩ f hf'
    simpa only [add_comm] using h

/-- Every actual support over the closed chord between these rays lies in
the same strict dual half-plane, including both endpoint fibres. -/
theorem normingFunctional_sum_pos_on_equal_norm_chord
    (a b : E) (L s : ℝ) (ha : ‖a‖ = L) (hb : ‖b‖ = L)
    (hdiff : ‖a - b‖ < 2 * L) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (f : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals ((1 - s) • a + s • b)) :
    0 < f (a + b) := by
  by_cases hs1 : s < 1
  · have hc : 0 < 1 - s := by linarith
    have hline : (1 - s) • (a + (s / (1 - s)) • b) =
        (1 - s) • a + s • b := by
      rw [smul_add, smul_smul, mul_div_cancel₀ s hc.ne']
    have hf' : f ∈ normingFunctionals (a + (s / (1 - s)) • b) := by
      rw [← normingFunctionals_pos_smul_eq (a + (s / (1 - s)) • b) (1 - s) hc,
        hline]
      exact hf
    exact normingFunctional_sum_pos_of_equal_norm_nonneg a b L (s / (1 - s))
      ha hb hdiff (div_nonneg hs.1 hc.le) f hf'
  · have hseq : s = 1 := by linarith [hs.2]
    have hf' : f ∈ normingFunctionals (b + (0 : ℝ) • a) := by
      simpa only [hseq, sub_self, zero_smul, one_smul, zero_add, add_zero] using hf
    have hdiff' : ‖b - a‖ < 2 * L := by
      rw [norm_sub_rev]
      exact hdiff
    have h := normingFunctional_sum_pos_of_equal_norm_nonneg b a L 0 hb ha hdiff'
      le_rfl f hf'
    simpa only [add_comm] using h

/-- The actual trace chord from the first axis to the second axis satisfies
the common strict half-plane conclusion. -/
theorem trace_normingFunctional_sum_pos_on_chord (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (f : StrongDual ℝ TracePlane)
    (hf : f ∈ normingFunctionals ((1 - s) • traceBasis 0 + s • traceBasis 1)) :
    0 < f (traceBasis 0 + traceBasis 1) :=
  normingFunctional_sum_pos_on_equal_norm_chord _ _ traceAxisLength s
    norm_traceBasis_zero norm_traceBasis_one norm_traceBasis_sub_lt_twice_axis hs f hf

end Markov
