import Markov.TraceCompatibility
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Uniform lower and coordinate-height upper bounds for the constructed
trace norm. Primitive interpolation is supplied by actual quadrant Farey
words and their propagated integer traces. -/

noncomputable section
namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Direct comparison with coordinate infinity height. -/
theorem intVector_norm_le_height (B : Module.Basis (Fin 2) ℝ E) (p : ℤ × ℤ) :
    ‖intVector B p‖ ≤ (‖B 0‖ + ‖B 1‖) * intHeight p := by
  calc
    ‖intVector B p‖ ≤ ‖(p.1 : ℝ) • B 0‖ + ‖(p.2 : ℝ) • B 1‖ := norm_add_le _ _
    _ = |(p.1 : ℝ)| * ‖B 0‖ + |(p.2 : ℝ)| * ‖B 1‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ intHeight p * ‖B 0‖ + intHeight p * ‖B 1‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    _ = _ := by ring

/-- Every primitive vector has an actual integer matrix trace at least three. -/
theorem primitive_tracePlane_trace (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    ∃ t : ℤ, 3 ≤ t ∧ (t : ℝ) = 2 * Real.cosh (‖intVector traceBasis p‖ / 2) := by
  obtain ⟨k, q, M, N, h, _⟩ := primitive_exists_quadrantSeededFarey_left p hp
  exact ⟨M.trace, (h.positiveFrickePair (quadrantSeed_positiveFrickePair k)).trace_left,
    (tracePlane_quadrantTraceLengthCompatible k h).1⟩

/-- The integer trace threshold implies the axis-length lower bound. -/
theorem traceAxisLength_le_of_trace_cosh (t ℓ : ℝ) (ht : 3 ≤ t)
    (hℓ : 0 ≤ ℓ) (htrace : t = 2 * Real.cosh (ℓ / 2)) :
    traceAxisLength ≤ ℓ := by
  have harg : (3 : ℝ) / 2 ≤ Real.cosh (ℓ / 2) := by linarith
  have hmono := (Real.arcosh_le_arcosh (by norm_num : (0 : ℝ) < 3 / 2)
    (Real.cosh_pos (ℓ / 2))).mpr harg
  rw [Real.arcosh_cosh (by positivity : 0 ≤ ℓ / 2)] at hmono
  unfold traceAxisLength
  linarith

/-- Every primitive integral direction has length at least the trace-axis length. -/
theorem traceAxisLength_le_norm_intVector (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    traceAxisLength ≤ ‖intVector traceBasis p‖ := by
  obtain ⟨t, ht, htrace⟩ := primitive_tracePlane_trace p hp
  exact traceAxisLength_le_of_trace_cosh (t : ℝ) _ (by exact_mod_cast ht)
    (norm_nonneg _) htrace

/-- A sharp elementary coordinate-height upper bound for the trace norm. -/
theorem tracePlane_norm_intVector_le_height (p : ℤ × ℤ) :
    ‖intVector traceBasis p‖ ≤ 2 * traceAxisLength * intHeight p := by
  simpa only [norm_traceBasis_zero, norm_traceBasis_one, ← two_mul] using
    intVector_norm_le_height traceBasis p

/-- The more generous upper bound obtained by passing through Euclidean height. -/
theorem tracePlane_norm_intVector_le_two_basis_height (p : ℤ × ℤ) :
    ‖intVector traceBasis p‖ ≤
      2 * (‖traceBasis 0‖ + ‖traceBasis 1‖) * intHeight p := by
  have h := intVector_norm_le_height traceBasis p
  have hnonneg : 0 ≤ (‖traceBasis 0‖ + ‖traceBasis 1‖) * intHeight p :=
    mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (intHeight_nonneg p)
  nlinarith

/-- Continuity of the coordinate map gives a positive uniform inverse
comparison for every norm on a real plane. -/
theorem exists_intVector_norm_ge_height (B : Module.Basis (Fin 2) ℝ E) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℤ × ℤ, c * intHeight p ≤ ‖intVector B p‖ := by
  letI : FiniteDimensional ℝ E := B.finiteDimensional_of_finite
  let f : E →L[ℝ] (Fin 2 → ℝ) := B.equivFun.toContinuousLinearEquiv.toContinuousLinearMap
  let C : ℝ := max ‖f‖ 1
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro p
  have hf : ‖f (intVector B p)‖ ≤ C * ‖intVector B p‖ :=
    (f.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hcoords : ∀ i : Fin 2,
      ‖f (intVector B p) i‖ ≤ C * ‖intVector B p‖ := fun i =>
    (norm_le_pi_norm _ i).trans hf
  have h0 : |(p.1 : ℝ)| ≤ C * ‖intVector B p‖ := by
    simpa [f, intVector, Module.Basis.equivFun_apply] using hcoords 0
  have h1 : |(p.2 : ℝ)| ≤ C * ‖intVector B p‖ := by
    simpa [f, intVector, Module.Basis.equivFun_apply] using hcoords 1
  have hh : intHeight p ≤ C * ‖intVector B p‖ := max_le h0 h1
  calc
    C⁻¹ * intHeight p ≤ C⁻¹ * (C * ‖intVector B p‖) :=
      mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hC.le)
    _ = ‖intVector B p‖ := by rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]

/-- One positive constant bounds the actual trace norm below by integer
coordinate height, for all integral directions. -/
theorem tracePlane_exists_height_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℤ × ℤ,
      c * intHeight p ≤ ‖intVector traceBasis p‖ :=
  exists_intVector_norm_ge_height traceBasis

end Markov
