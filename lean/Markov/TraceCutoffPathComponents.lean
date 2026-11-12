import Markov.TraceUnresolvedAssociation
import Markov.SignedCutoffArcEmbedding
import Markov.BoundaryWedgeInclusion
import Markov.ChordRationalSupport

/-! Actual real-cutoff components are exact open arcs of the single
traversal trace-boundary path. Rational endpoint order is reversed in the
orientation-reversing signed sectors, with both actual endpoints marked. -/

noncomputable section
open Set
namespace Markov

/-- Every point between two rational quadrant rays is a normalized
strictly positive combination of the original integer endpoint vectors. -/
theorem SeededFarey.mem_trace_rational_arc_exists_pos_intVector_combination
    {q : Fin 4} {u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections q).1 (quadrantSeedDirections q).2
      M0 N0 u v M N) (x : TracePlane)
    (hx : x ∈ traceBoundaryOpenArc (traceRationalParameter q u)
      (traceRationalParameter q v)) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      NormedSpace.normalize (α • intVector traceBasis u + β • intVector traceBasis v) = x := by
  rcases hx with ⟨t, ht, rfl⟩
  let a := traceRationalQuarterParameter q u
  let b := traceRationalQuarterParameter q v
  let s := t - (q.val : ℝ)
  have ha := h.traceRationalQuarterParameter_left_mem_Icc
  have hb := h.traceRationalQuarterParameter_right_mem_Icc
  have hab : a < b := h.traceRationalQuarterParameter_lt
  have hs : s ∈ Ioo a b := by
    dsimp [s, a, b, traceRationalParameter] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans hs.1.le, hs.2.le.trans hb.2⟩
  have hu := profileMass_pos _ h.quadrant_left_nonnegativePrimitive
  have hv := profileMass_pos _ h.quadrant_right_nonnegativePrimitive
  have hU : intVector traceBasis u = profileMass (quadrantCoordinates q u) •
      ((1 - a) • traceRotationBasis q.val 0 + a • traceRotationBasis q.val 1) := by
    calc
      intVector traceBasis u =
          ((quadrantCoordinates q u).1 : ℝ) • traceRotationBasis q.val 0 +
          ((quadrantCoordinates q u).2 : ℝ) • traceRotationBasis q.val 1 :=
        (traceRotationBasis_quadrantCoordinates q u).symm
      _ = _ := intVector_eq_profileMass_smul_chordPoint _ _ hu.ne'
  have hV : intVector traceBasis v = profileMass (quadrantCoordinates q v) •
      ((1 - b) • traceRotationBasis q.val 0 + b • traceRotationBasis q.val 1) := by
    calc
      intVector traceBasis v =
          ((quadrantCoordinates q v).1 : ℝ) • traceRotationBasis q.val 0 +
          ((quadrantCoordinates q v).2 : ℝ) • traceRotationBasis q.val 1 :=
        (traceRotationBasis_quadrantCoordinates q v).symm
      _ = _ := intVector_eq_profileMass_smul_chordPoint _ _ hv.ne'
  refine ⟨(b - s) / profileMass (quadrantCoordinates q u),
    (s - a) / profileMass (quadrantCoordinates q v),
    div_pos (sub_pos.mpr hs.2) hu, div_pos (sub_pos.mpr hs.1) hv, ?_⟩
  have htEq : t = (q.val : ℝ) + s := by dsimp [s]; ring
  rw [htEq, traceBoundaryPath_add_eq_chordBoundarySection q s hsI,
    chordBoundarySection_eq_normalize, hU, hV, smul_smul, smul_smul,
    div_mul_cancel₀ _ hu.ne', div_mul_cancel₀ _ hv.ne']
  have he :
      (b - s) • ((1 - a) • traceRotationBasis q.val 0 + a • traceRotationBasis q.val 1) +
        (s - a) • ((1 - b) • traceRotationBasis q.val 0 + b • traceRotationBasis q.val 1) =
      (b - a) • ((1 - s) • traceRotationBasis q.val 0 + s • traceRotationBasis q.val 1) := by
    module
  rw [he, NormedSpace.normalize_smul_of_pos (sub_pos.mpr hab)]

/-- A positive combination of two ordered lattice rays lies on their
actual open slope arc in the unchanged norm. -/
theorem normalize_pos_intVector_combination_mem_slopeBoundaryArc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ)
    (hu : 0 < u.1) (hv : 0 < v.1) (hdet : intDet u v = 1)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    NormedSpace.normalize (α • intVector B u + β • intVector B v) ∈
      slopeBoundaryArc B (cutoffSlope u) (cutoffSlope v) := by
  have hd : intDet u v ≠ 0 := by omega
  have he := normalize_basis_combination (intPairBasis B u v hd) α β hα
  simp only [intPairBasis_zero, intPairBasis_one] at he
  rw [he]
  exact radial_intPairBasis_mem_slopeBoundaryArc B u v hd hu hv (by omega)
    (β / α) (div_pos hβ hα)

/-- Exact rational quadrant path arcs for all signed cutoff components.
Reflected sectors use the reversed original endpoint order. -/
theorem signedCutoffArc_exists_quadrant_word_eq
    (n : ℕ) (k : Fin 8) (u v : ℤ × ℤ) (h : ConsecutiveCutoffSlopes n u v) :
    ∃ (q : Fin 4) (M N : IntMatrixTwo),
      (SeededFarey (quadrantSeedDirections q).1 (quadrantSeedDirections q).2
          (quadrantSeedMatrices q).1 (quadrantSeedMatrices q).2
          (inverseSignedSectorCoordinates k u) (inverseSignedSectorCoordinates k v) M N ∧
        slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) =
          traceBoundaryOpenArc
            (traceRationalParameter q (inverseSignedSectorCoordinates k u))
            (traceRationalParameter q (inverseSignedSectorCoordinates k v))) ∨
      (SeededFarey (quadrantSeedDirections q).1 (quadrantSeedDirections q).2
          (quadrantSeedMatrices q).1 (quadrantSeedMatrices q).2
          (inverseSignedSectorCoordinates k v) (inverseSignedSectorCoordinates k u) M N ∧
        slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) =
          traceBoundaryOpenArc
            (traceRationalParameter q (inverseSignedSectorCoordinates k v))
            (traceRationalParameter q (inverseSignedSectorCoordinates k u))) := by
  have hu := ((mem_cutoffSlopesUpTo n u).mp h.1).1
  have hv := ((mem_cutoffSlopesUpTo n v).mp h.2.1).1
  have hd := (consecutiveCutoffSlopes_det_and_denominator_sum n u v h).1
  obtain ⟨q, M, N, ⟨hword, hsub⟩ | ⟨hword, hsub⟩⟩ :=
    signedCutoffArc_exists_quadrant_word n k u v h
  · refine ⟨q, M, N, Or.inl ⟨hword, Set.Subset.antisymm hsub ?_⟩⟩
    intro x hx
    obtain ⟨α, β, hα, hβ, he⟩ :=
      hword.mem_trace_rational_arc_exists_pos_intVector_combination x hx
    have hm := normalize_pos_intVector_combination_mem_slopeBoundaryArc
      (signedSectorBasis traceBasis k) u v hu hv hd α β hα hβ
    rw [signedSectorBasis_intVector_inverse, signedSectorBasis_intVector_inverse, he] at hm
    exact hm
  · refine ⟨q, M, N, Or.inr ⟨hword, Set.Subset.antisymm hsub ?_⟩⟩
    intro x hx
    obtain ⟨α, β, hα, hβ, he⟩ :=
      hword.mem_trace_rational_arc_exists_pos_intVector_combination x hx
    have hm := normalize_pos_intVector_combination_mem_slopeBoundaryArc
      (signedSectorBasis traceBasis k) u v hu hv hd β α hβ hα
    rw [signedSectorBasis_intVector_inverse, signedSectorBasis_intVector_inverse] at hm
    rw [add_comm] at he
    rw [he] at hm
    exact hm

/-- Correctly oriented rational parameters lie within one traversal. -/
theorem SeededFarey.traceRationalParameter_bounds
    {q : Fin 4} {u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections q).1 (quadrantSeedDirections q).2
      M0 N0 u v M N) :
    0 ≤ traceRationalParameter q u ∧ traceRationalParameter q u < traceRationalParameter q v ∧
      traceRationalParameter q v ≤ 4 := by
  have hu := h.traceRationalQuarterParameter_left_mem_Icc
  have hv := h.traceRationalQuarterParameter_right_mem_Icc
  have hq0 : (0 : ℝ) ≤ q.val := Nat.cast_nonneg _
  have hq3 : (q.val : ℝ) ≤ 3 := by exact_mod_cast (show q.val ≤ 3 by omega)
  refine ⟨?_, h.traceRationalParameter_lt, ?_⟩ <;>
    dsimp [traceRationalParameter] <;> linarith [hu.1, hv.2]

private theorem inverseSigned_cutoff_endpoint_mem_realCutoffCorners
    (H : ℝ) (hH : 0 ≤ H) (k : Fin 8) (u : ℤ × ℤ) (hu : u ∈ cutoffSlopesUpTo ⌊H⌋₊) :
    NormedSpace.normalize (intVector traceBasis (inverseSignedSectorCoordinates k u)) ∈
      realCutoffCorners traceBasis H := by
  rw [realCutoffCorners_eq_natFloor traceBasis H hH]
  have hm := normalize_mem_cutoffCorners (signedSectorBasis traceBasis k) ⌊H⌋₊ u hu
  rw [signedSectorBasis_intVector_inverse, cutoffCorners_signedSectorBasis] at hm
  exact hm

/-- Every actual real-cutoff component is exactly an open path interval
inside one traversal, with both path endpoints in the actual cutoff. -/
theorem traceUncutBoundary_exists_path_component
    (H : ℝ) (hH : 1 ≤ H) (x : TracePlane) (hx : x ∈ traceUncutBoundary H) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 4 ∧
      traceBoundaryPath a ∈ realCutoffCorners traceBasis H ∧
      traceBoundaryPath b ∈ realCutoffCorners traceBasis H ∧
      connectedComponentIn (traceUncutBoundary H) x = traceBoundaryOpenArc a b := by
  obtain ⟨k, u, v, h, _, hcomp⟩ :=
    traceUncutBoundary_exists_signed_cutoff_component H hH x hx
  have hu := inverseSigned_cutoff_endpoint_mem_realCutoffCorners H
    (le_trans (by norm_num) hH) k u h.1
  have hv := inverseSigned_cutoff_endpoint_mem_realCutoffCorners H
    (le_trans (by norm_num) hH) k v h.2.1
  obtain ⟨q, M, N, ⟨hword, heq⟩ | ⟨hword, heq⟩⟩ :=
    signedCutoffArc_exists_quadrant_word_eq ⌊H⌋₊ k u v h
  · obtain ⟨ha, hab, hb⟩ := hword.traceRationalParameter_bounds
    refine ⟨_, _, ha, hab, hb, ?_, ?_, hcomp.trans heq⟩
    · rwa [hword.traceBoundaryPath_traceRationalParameter_left]
    · rwa [hword.traceBoundaryPath_traceRationalParameter_right]
  · obtain ⟨ha, hab, hb⟩ := hword.traceRationalParameter_bounds
    refine ⟨_, _, ha, hab, hb, ?_, ?_, hcomp.trans heq⟩
    · rwa [hword.traceBoundaryPath_traceRationalParameter_left]
    · rwa [hword.traceBoundaryPath_traceRationalParameter_right]

end Markov
