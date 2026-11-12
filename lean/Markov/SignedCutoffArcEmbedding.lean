import Markov.SignedCutoffTurnDecay
import Markov.TraceBoundaryNormalTurn
import Markov.TailPolynomialAbsorption

/-! Every signed cutoff component embeds in an actual rational quadrant
arc. The actual supports on that enclosing arc give uniform exponential
normal-diameter decay, including the orientation-reversing sectors. -/

noncomputable section
open Set
namespace Markov

/-- Actual quadrant words and an enclosing boundary arc for every signed
cutoff component. Reflected sectors use the reversed actual endpoints. -/
theorem signedCutoffArc_exists_quadrant_word
    (H : ℕ) (k : Fin 8) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H u v) :
    ∃ (q : Fin 4) (M N : IntMatrixTwo),
      (SeededFarey (quadrantSeedDirections q).1 (quadrantSeedDirections q).2
          (quadrantSeedMatrices q).1 (quadrantSeedMatrices q).2
          (inverseSignedSectorCoordinates k u) (inverseSignedSectorCoordinates k v) M N ∧
        slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) ⊆
          traceBoundaryOpenArc
            (traceRationalParameter q (inverseSignedSectorCoordinates k u))
            (traceRationalParameter q (inverseSignedSectorCoordinates k v))) ∨
      (SeededFarey (quadrantSeedDirections q).1 (quadrantSeedDirections q).2
          (quadrantSeedMatrices q).1 (quadrantSeedMatrices q).2
          (inverseSignedSectorCoordinates k v) (inverseSignedSectorCoordinates k u) M N ∧
        slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) ⊆
          traceBoundaryOpenArc
            (traceRationalParameter q (inverseSignedSectorCoordinates k v))
            (traceRationalParameter q (inverseSignedSectorCoordinates k u))) := by
  obtain ⟨_, hu0, hu1, _, _⟩ := (mem_cutoffSlopesUpTo H u).mp h.1
  obtain ⟨_, hv0, hv1, _, _⟩ := (mem_cutoffSlopesUpTo H v).mp h.2.1
  obtain ⟨q, M, N, _, _, _, _, _, _, hforward | hreverse⟩ :=
    signedSector_exists_quadrantSeededFarey k u v hu0 hu1 hv0 hv1
      (consecutiveCutoffSlopes_det_and_denominator_sum H u v h).1
  · refine ⟨q, M, N, Or.inl ⟨hforward.2, ?_⟩⟩
    intro x hx
    obtain ⟨α, β, hα, hβ, he⟩ :=
      consecutiveCutoffSlopes_mem_arc_exists_pos_intVector_combination
        (signedSectorBasis traceBasis k) H u v h x hx
    rw [signedSectorBasis_intVector_inverse, signedSectorBasis_intVector_inverse] at he
    rw [← he]
    exact hforward.2.normalize_positiveCombination_mem_traceBoundaryOpenArc α β hα hβ
  · refine ⟨q, M, N, Or.inr ⟨hreverse.2, ?_⟩⟩
    intro x hx
    obtain ⟨α, β, hα, hβ, he⟩ :=
      consecutiveCutoffSlopes_mem_arc_exists_pos_intVector_combination
        (signedSectorBasis traceBasis k) H u v h x hx
    rw [signedSectorBasis_intVector_inverse, signedSectorBasis_intVector_inverse] at he
    rw [← he]
    simpa only [add_comm] using
      hreverse.2.normalize_positiveCombination_mem_traceBoundaryOpenArc β α hβ hα

/-- The actual normals over any subset of a rational quadrant arc are
bounded by the complete turn of that arc. -/
theorem SeededFarey.normals_diam_le_trace_rational_arc_turn
    {q : Fin 4} {u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections q).1 (quadrantSeedDirections q).2
      M0 N0 u v M N) (S : Set TracePlane)
    (hS : S ⊆ traceBoundaryOpenArc
      (traceRationalParameter q u) (traceRationalParameter q v)) :
    Metric.diam (normalsOn traceBasis S) ≤
      (traceBoundaryTurn (traceBoundaryOpenArc
        (traceRationalParameter q u) (traceRationalParameter q v))).toReal := by
  have hu := h.traceRationalQuarterParameter_left_mem_Icc
  have hv := h.traceRationalQuarterParameter_right_mem_Icc
  have hq0 : (0 : ℝ) ≤ q.val := Nat.cast_nonneg _
  have hq3 : (q.val : ℝ) ≤ 3 := by exact_mod_cast (show q.val ≤ 3 by omega)
  have ha : 0 ≤ traceRationalParameter q u := by
    dsimp [traceRationalParameter]
    linarith [hu.1]
  have hb : traceRationalParameter q v ≤ 4 := by
    dsimp [traceRationalParameter]
    linarith [hv.2]
  exact (Metric.diam_mono (normalsOn_mono traceBasis hS)
    (normalsOn_isBounded traceBasis _)).trans
      (traceBoundaryOpenArc_normals_diam_le_turn _ _ ha h.traceRationalParameter_lt hb)

/-- Uniform height decay of the actual normal diameter of every signed
cutoff component, measured throughout in the original trace basis. -/
theorem signed_cutoff_normal_diam_height_decay :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (H : ℕ) (k : Fin 8) (u v : ℤ × ℤ),
      ConsecutiveCutoffSlopes H u v →
      Metric.diam (normalsOn traceBasis
        (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))) ≤
        C * (intHeight u + intHeight v) *
          Real.exp (-(c * (intHeight u + intHeight v))) := by
  obtain ⟨C, c, hC, hc, hdecay⟩ := trace_rational_arc_turn_height_decay
  refine ⟨C, c, hC, hc, ?_⟩
  intro H k u v h
  obtain ⟨_, _, _, _, _, _, _, _, hheight, _⟩ :=
    signedConsecutiveCutoffSlopes_height_bounds k H u v h
  obtain ⟨q, M, N, ⟨hword, hsub⟩ | ⟨hword, hsub⟩⟩ :=
    signedCutoffArc_exists_quadrant_word H k u v h
  · have hdiam := hword.normals_diam_le_trace_rational_arc_turn _ hsub
    have hb := hdecay q _ _ M N hword hheight
    simpa only [inverseSignedSectorCoordinates_height] using hdiam.trans hb
  · have hdiam := hword.normals_diam_le_trace_rational_arc_turn _ hsub
    have hheight' : 1 < intHeight
        (inverseSignedSectorCoordinates k v + inverseSignedSectorCoordinates k u) := by
      simpa only [add_comm] using hheight
    have hb := hdecay q _ _ M N hword hheight'
    simpa only [inverseSignedSectorCoordinates_height, add_comm] using hdiam.trans hb

/-- The actual signed normal diameter has a uniform `H exp(-c H)` bound. -/
theorem signed_cutoff_normal_diam_cutoff_decay :
    ∃ D c : ℝ, 0 < D ∧ 0 < c ∧ ∀ (H : ℕ) (k : Fin 8) (u v : ℤ × ℤ),
      ConsecutiveCutoffSlopes H u v →
      Metric.diam (normalsOn traceBasis
        (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))) ≤
        D * (H : ℝ) * Real.exp (-(c * (H : ℝ))) := by
  obtain ⟨C, c, hC, hc, hdecay⟩ := signed_cutoff_normal_diam_height_decay
  refine ⟨2 * C, c, mul_pos (by norm_num) hC, hc, ?_⟩
  intro H k u v h
  obtain ⟨_, _, _, _, _, _, hsumH, hsum2H, _, _⟩ :=
    signedConsecutiveCutoffSlopes_height_bounds k H u v h
  simp only [inverseSignedSectorCoordinates_height] at hsumH hsum2H
  apply (hdecay H k u v h).trans
  have he : Real.exp (-(c * (intHeight u + intHeight v))) ≤
      Real.exp (-(c * (H : ℝ))) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hsumH.le hc.le))
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hsum2H hC.le) he
    (Real.exp_pos _).le (mul_nonneg hC.le (by positivity : (0 : ℝ) ≤ 2 * H))
  convert hh using 1
  ring

/-- Unconditional uniform exponential decay of the actual signed cutoff
normal diameters. In particular no reflected-norm symmetry is required. -/
theorem signed_cutoff_normal_diam_decay :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ (H : ℕ), 1 ≤ H →
      ∀ (k : Fin 8) (u v : ℤ × ℤ), ConsecutiveCutoffSlopes H u v →
        Metric.diam (normalsOn traceBasis
          (slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v))) ≤
          M * Real.exp (-c * (H : ℝ)) := by
  obtain ⟨D, c, hD, hc, hdecay⟩ := signed_cutoff_normal_diam_cutoff_decay
  refine ⟨D * (48 / c ^ 3), c / 2, by positivity, by positivity, ?_⟩
  intro H hH k u v h
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hcube : (H : ℝ) ≤ (H : ℝ) ^ 3 := by
    nlinarith [sq_nonneg ((H : ℝ) - 1)]
  have hp := cube_mul_exp_neg_le_half_rate c (H : ℝ) hc (Nat.cast_nonneg _)
  calc
    _ ≤ D * (H : ℝ) * Real.exp (-c * (H : ℝ)) := by
      simpa only [neg_mul] using hdecay H k u v h
    _ ≤ D * ((H : ℝ) ^ 3 * Real.exp (-c * (H : ℝ))) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcube hD.le) (Real.exp_pos _).le
    _ ≤ D * ((48 / c ^ 3) * Real.exp (-(c / 2) * (H : ℝ))) :=
      mul_le_mul_of_nonneg_left hp hD.le
    _ = _ := by ring

end Markov
