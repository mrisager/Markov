import Markov.TraceSupportDeficit
import Markov.SupportGapCoordinates
import Markov.PrimitiveTraceBounds
import Markov.NormingCovectorRadius

/-! Exponential closeness of the two inward endpoint supports
of a quadrant Farey gap. -/

noncomputable section

namespace Markov

/-- The actual inward support covectors are exponentially close in the
sum of endpoint lengths, with only a linear endpoint-height loss. -/
theorem SeededFarey.trace_inward_covector_gap (k : Fin 4)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N)
    (hheight : 1 < intHeight (u + v)) :
    dist (euclideanDualCoordinates traceBasis (selectedSupportAt traceBasis u v))
        (euclideanDualCoordinates traceBasis (selectedSupportAt traceBasis v u)) ≤
      192 * (intHeight u + intHeight v) *
        Real.exp (-‖intVector traceBasis u‖ - ‖intVector traceBasis v‖) := by
  have hd : intDet u v = 1 := h.det_eq_seed.trans (quadrantSeed_det_eq_one k)
  have hd0 : intDet u v ≠ 0 := by simp [hd]
  have hdr : intDet v u ≠ 0 := by
    simp only [intDet] at *
    intro hz
    nlinarith
  have hb := h.trace_support_deficit_exp_bounds k hheight
  have hu : |selectedSupportAt traceBasis u v (intVector traceBasis u) -
      selectedSupportAt traceBasis v u (intVector traceBasis u)| ≤
        96 * Real.exp (-‖intVector traceBasis u‖ - ‖intVector traceBasis v‖) := by
    rw [selectedSupportAt_value_self traceBasis u v hd0, abs_of_nonneg hb.1.1]
    exact hb.1.2
  have hv : |selectedSupportAt traceBasis u v (intVector traceBasis v) -
      selectedSupportAt traceBasis v u (intVector traceBasis v)| ≤
        96 * Real.exp (-‖intVector traceBasis u‖ - ‖intVector traceBasis v‖) := by
    rw [selectedSupportAt_value_self traceBasis v u hdr, abs_sub_comm,
      abs_of_nonneg hb.2.1]
    exact hb.2.2
  have hh := euclideanDualCoordinates_dist_le_uniform_pair_values traceBasis
    (selectedSupportAt traceBasis u v) (selectedSupportAt traceBasis v u)
    u v (by simp [hd]) _ hu hv
  convert hh using 1
  ring

/-- A single positive decay rate controls all actual inward covector
gaps by the sum of their endpoint coordinate heights. -/
theorem trace_inward_covector_gap_height_decay :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : Fin 4) (u v : ℤ × ℤ) (M N : IntMatrixTwo),
      SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
        (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N →
      1 < intHeight (u + v) →
      dist (euclideanDualCoordinates traceBasis (selectedSupportAt traceBasis u v))
          (euclideanDualCoordinates traceBasis (selectedSupportAt traceBasis v u)) ≤
        192 * (intHeight u + intHeight v) *
          Real.exp (-(c * (intHeight u + intHeight v))) := by
  obtain ⟨c, hc, hbound⟩ := tracePlane_exists_height_lower_bound
  refine ⟨c, hc, ?_⟩
  intro k u v M N h hheight
  apply (h.trace_inward_covector_gap k hheight).trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (by norm_num) (add_nonneg (intHeight_nonneg u) (intHeight_nonneg v)))
  apply Real.exp_le_exp.mpr
  nlinarith [hbound u, hbound v]

/-- The inward endpoint normals retain a uniform exponential
height estimate after normalization. -/
theorem trace_inward_normal_gap_height_decay :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (k : Fin 4) (u v : ℤ × ℤ) (M N : IntMatrixTwo),
      SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
        (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N →
      1 < intHeight (u + v) →
      dist (normalizedEuclideanCovector traceBasis (selectedSupportAt traceBasis u v))
          (normalizedEuclideanCovector traceBasis (selectedSupportAt traceBasis v u)) ≤
        C * (intHeight u + intHeight v) *
          Real.exp (-(c * (intHeight u + intHeight v))) := by
  obtain ⟨c, hc, hcov⟩ := trace_inward_covector_gap_height_decay
  have hK : 0 < 2 / traceNormingCovectorRadius :=
    div_pos (by norm_num) traceNormingCovectorRadius_pos
  refine ⟨(2 / traceNormingCovectorRadius) * 192, c,
    mul_pos hK (by norm_num), hc, ?_⟩
  intro k u v M N h hheight
  have hp := h.positiveFrickePair (quadrantSeed_positiveFrickePair k)
  have hcompat := tracePlane_quadrantTraceLengthCompatible k h
  have hulo : traceAxisLength ≤ ‖intVector traceBasis u‖ :=
    traceAxisLength_le_of_trace_cosh M.trace _ (by exact_mod_cast hp.trace_left)
      (norm_nonneg _) hcompat.1
  have hvlo : traceAxisLength ≤ ‖intVector traceBasis v‖ :=
    traceAxisLength_le_of_trace_cosh N.trace _ (by exact_mod_cast hp.trace_right)
      (norm_nonneg _) hcompat.2
  have hun : intVector traceBasis u ≠ 0 := norm_pos_iff.mp
    (traceAxisLength_pos.trans_le hulo)
  have hvn : intVector traceBasis v ≠ 0 := norm_pos_iff.mp
    (traceAxisLength_pos.trans_le hvlo)
  have hd : intDet u v = 1 := h.det_eq_seed.trans (quadrantSeed_det_eq_one k)
  have hd0 : intDet u v ≠ 0 := by simp [hd]
  have hdr : intDet v u ≠ 0 := by
    simp only [intDet] at *
    intro hz
    nlinarith
  have hn := traceNormingCovector_normalize_dist_le _ _ hun hvn
    (selectedSupportAt traceBasis u v) (selectedSupportAt traceBasis v u)
    (selectedSupportAt_spec traceBasis u v hd0).1
    (selectedSupportAt_spec traceBasis v u hdr).1
  have hh := mul_le_mul_of_nonneg_left (hcov k u v M N h hheight) hK.le
  apply hn.trans
  convert hh using 1
  ring

end Markov
