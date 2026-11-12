import Markov.BirthSelectedValues
import Markov.BirthCornerJump
import Markov.CornerSupportDeterminant
import Markov.PrimitiveTraceBounds

/-! Quantitative bounds for the trace norm's boundary atom at
each quadrant Farey birth, with trace compatibility and the selected
covector evaluations proved for the constructed norm. -/

noncomputable section
attribute [-instance] DivisionRing.toRatAlgebra
local instance : Algebra ℚ ℝ := DivisionRing.toRatAlgebra

namespace Markov

/-- The jump between the actual selected birth supports is the explicit
positive logarithmic trace expression. -/
theorem SeededFarey.trace_birth_support_jump (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N) :
    selectedSupportAt traceBasis (u + v) u (intVector traceBasis u) -
      selectedSupportAt traceBasis (u + v) v (intVector traceBasis u) =
      analyticCornerJump (M * N).trace := by
  have hp := h.positiveFrickePair (quadrantSeed_positiveFrickePair k)
  letI : Fact (3 ≤ (M * N).trace) := ⟨hp.trace_product⟩
  have hd : intDet u v = 1 := h.det_eq_seed.trans (quadrantSeed_det_eq_one k)
  have hdv : intDet (u + v) v ≠ 0 := by
    simp only [intDet, Prod.fst_add, Prod.snd_add] at *
    nlinarith
  have hvals := h.trace_birth_selected_values k
  exact birth_norming_support_jump traceBasis u v
    (selectedSupportAt traceBasis (u + v) u) (selectedSupportAt traceBasis (u + v) v)
    (selectedSupportAt_spec traceBasis (u + v) v hdv).1
    (M * N).trace M.trace N.trace (by linarith [hp.trace_left])
    (by nlinarith [hp.fricke])
    (tracePlane_quadrantTraceLengthCompatible k h.right).1 hvals.1 hvals.2

/-- A Farey birth is a genuine nonzero corner, with a lower bound in
terms of its actual trace and actual trace-norm length. -/
theorem SeededFarey.trace_birth_atom_lower (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N) :
    ‖intVector traceBasis (u + v)‖ * analyticCornerJump (M * N).trace /
        (‖traceBasis 0‖ + ‖traceBasis 1‖) ^ 2 ≤
      (traceBoundaryTurn {NormedSpace.normalize (intVector traceBasis (u + v))}).toReal := by
  have hp := h.positiveFrickePair (quadrantSeed_positiveFrickePair k)
  have hd : intDet u v = 1 := h.det_eq_seed.trans (quadrantSeed_det_eq_one k)
  have hdu : intDet (u + v) u ≠ 0 := by
    simp only [intDet, Prod.fst_add, Prod.snd_add] at *
    nlinarith
  have hdv : intDet (u + v) v ≠ 0 := by
    simp only [intDet, Prod.fst_add, Prod.snd_add] at *
    nlinarith
  have hlower : traceAxisLength ≤ ‖intVector traceBasis (u + v)‖ :=
    traceAxisLength_le_of_trace_cosh (M * N).trace _
      (by exact_mod_cast hp.trace_product) (norm_nonneg _)
      (tracePlane_quadrantTraceLengthCompatible k h.right).1
  have hne : intVector traceBasis (u + v) ≠ 0 :=
    norm_pos_iff.mp (traceAxisLength_pos.trans_le hlower)
  have hb := traceBoundaryTurn_atom_lower_of_support_jump u v (by simp [hd]) hne
    (selectedSupportAt traceBasis (u + v) u) (selectedSupportAt traceBasis (u + v) v)
    (selectedSupportAt_spec traceBasis (u + v) u hdu).1
    (selectedSupportAt_spec traceBasis (u + v) v hdv).1
    (analyticCornerJump (M * N).trace) (h.trace_birth_support_jump k)
  rwa [abs_of_pos (analyticCornerJump_pos _ (by exact_mod_cast hp.trace_product))] at hb

/-- The actual birth atom has the expected exponential lower bound in
its norm length, with an explicit fixed coordinate constant. -/
theorem SeededFarey.trace_birth_atom_exp_lower (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N) :
    2 * ‖intVector traceBasis (u + v)‖ * Real.exp (-‖intVector traceBasis (u + v)‖) /
        (‖traceBasis 0‖ + ‖traceBasis 1‖) ^ 2 ≤
      (traceBoundaryTurn {NormedSpace.normalize (intVector traceBasis (u + v))}).toReal := by
  have hp := h.positiveFrickePair (quadrantSeed_positiveFrickePair k)
  have hj := analyticCornerJump_ge_two_exp_neg_of_cosh (M * N).trace
    ‖intVector traceBasis (u + v)‖ (by exact_mod_cast hp.trace_product) (norm_nonneg _)
    (tracePlane_quadrantTraceLengthCompatible k h.right).1
  apply le_trans _ (h.trace_birth_atom_lower k)
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hj (norm_nonneg (intVector traceBasis (u + v)))]

/-- A uniform height-cutoff lower bound for every actual birth atom. -/
theorem SeededFarey.trace_birth_atom_height_lower (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N)
    (H : ℝ) (hH : intHeight (u + v) ≤ H) :
    (2 * traceAxisLength / (‖traceBasis 0‖ + ‖traceBasis 1‖) ^ 2) *
        Real.exp (-(2 * traceAxisLength * H)) ≤
      (traceBoundaryTurn {NormedSpace.normalize (intVector traceBasis (u + v))}).toReal := by
  have hp := h.positiveFrickePair (quadrantSeed_positiveFrickePair k)
  have hlo : traceAxisLength ≤ ‖intVector traceBasis (u + v)‖ :=
    traceAxisLength_le_of_trace_cosh (M * N).trace _
      (by exact_mod_cast hp.trace_product) (norm_nonneg _)
      (tracePlane_quadrantTraceLengthCompatible k h.right).1
  have hhi : ‖intVector traceBasis (u + v)‖ ≤ 2 * traceAxisLength * H :=
    (tracePlane_norm_intVector_le_height _).trans
      (mul_le_mul_of_nonneg_left hH (mul_nonneg (by norm_num) traceAxisLength_pos.le))
  have he := Real.exp_le_exp.mpr (neg_le_neg hhi)
  apply le_trans _ (h.trace_birth_atom_exp_lower k)
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hlo (by norm_num)) he
    (Real.exp_pos _).le (mul_nonneg (by norm_num) (norm_nonneg _))

end Markov
