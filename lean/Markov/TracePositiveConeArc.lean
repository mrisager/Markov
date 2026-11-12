import Markov.TraceRationalParameters
import Markov.TraceBoundaryOpenArcs

/-! Strictly positive combinations of an oriented pair of quadrant
directions lie on the actual open trace-boundary arc between those rays. -/

noncomputable section
open Set

namespace Markov

/-- A positive weighted ratio lies strictly between its endpoint ratios. -/
theorem positive_weightedRatio_mem_Ioo (bu bv mu mv α β : ℝ)
    (hmu : 0 < mu) (hmv : 0 < mv) (hα : 0 < α) (hβ : 0 < β)
    (hlt : bu / mu < bv / mv) :
    (α * bu + β * bv) / (α * mu + β * mv) ∈ Ioo (bu / mu) (bv / mv) := by
  have hden : 0 < α * mu + β * mv := add_pos (mul_pos hα hmu) (mul_pos hβ hmv)
  have hc : bu * mv < bv * mu := (div_lt_div_iff₀ hmu hmv).mp hlt
  constructor
  · apply (div_lt_div_iff₀ hmu hden).mpr
    nlinarith [mul_pos hβ (sub_pos.mpr hc)]
  · apply (div_lt_div_iff₀ hden hmv).mpr
    nlinarith [mul_pos hα (sub_pos.mpr hc)]

/-- The chord parameter of a positive real combination of two integer rays. -/
def positiveCombinationQuarterParameter (k : Fin 4) (u v : ℤ × ℤ) (α β : ℝ) : ℝ :=
  (α * ((quadrantCoordinates k u).2 : ℝ) + β * ((quadrantCoordinates k v).2 : ℝ)) /
    (α * profileMass (quadrantCoordinates k u) + β * profileMass (quadrantCoordinates k v))

/-- Positive combinations occur strictly between the oriented endpoint
parameters whenever the endpoint coordinate masses are positive. -/
theorem positiveCombinationQuarterParameter_mem_Ioo
    (k : Fin 4) (u v : ℤ × ℤ) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hu : 0 < profileMass (quadrantCoordinates k u))
    (hv : 0 < profileMass (quadrantCoordinates k v)) (hd : intDet u v = 1) :
    positiveCombinationQuarterParameter k u v α β ∈
      Ioo (traceRationalQuarterParameter k u) (traceRationalQuarterParameter k v) := by
  exact positive_weightedRatio_mem_Ioo _ _ _ _ _ _ hu hv hα hβ
    (traceRationalQuarterParameter_lt_of_det_one k u v hu hv hd)

/-- The normalized chord at the mixture ratio is the normalized actual
real combination, using the constructed trace norm throughout. -/
theorem chordBoundarySection_positiveCombinationQuarterParameter
    (k : Fin 4) (u v : ℤ × ℤ) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hu : 0 < profileMass (quadrantCoordinates k u))
    (hv : 0 < profileMass (quadrantCoordinates k v)) :
    chordBoundarySection (traceRotationBasis k.val)
        (positiveCombinationQuarterParameter k u v α β) =
      NormedSpace.normalize (α • intVector traceBasis u + β • intVector traceBasis v) := by
  let a : ℝ := α * ((quadrantCoordinates k u).1 : ℝ) +
    β * ((quadrantCoordinates k v).1 : ℝ)
  let b : ℝ := α * ((quadrantCoordinates k u).2 : ℝ) +
    β * ((quadrantCoordinates k v).2 : ℝ)
  have hsum : a + b = α * profileMass (quadrantCoordinates k u) +
      β * profileMass (quadrantCoordinates k v) := by
    dsimp [a, b, profileMass]
    ring
  have hpos : 0 < a + b := by
    rw [hsum]
    exact add_pos (mul_pos hα hu) (mul_pos hβ hv)
  have hs : positiveCombinationQuarterParameter k u v α β = b / (a + b) := by
    rw [hsum]
    rfl
  have hvec : a • traceRotationBasis k.val 0 + b • traceRotationBasis k.val 1 =
      α • intVector traceBasis u + β • intVector traceBasis v := by
    rw [← traceRotationBasis_quadrantCoordinates k u,
      ← traceRotationBasis_quadrantCoordinates k v]
    dsimp [a, b]
    module
  rw [hs, chordBoundarySection_ratio_eq_normalize _ _ _ hpos, hvec]

/-- Every strictly positive real combination of an oriented pair in one
quadrant lies on the actual open boundary arc between its rational rays. -/
theorem normalize_positiveCombination_mem_traceBoundaryOpenArc
    (k : Fin 4) (u v : ℤ × ℤ) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hu0 : 0 ≤ (quadrantCoordinates k u).1)
    (hu1 : 0 ≤ (quadrantCoordinates k u).2)
    (hv0 : 0 ≤ (quadrantCoordinates k v).1)
    (hv1 : 0 ≤ (quadrantCoordinates k v).2)
    (hu : 0 < profileMass (quadrantCoordinates k u))
    (hv : 0 < profileMass (quadrantCoordinates k v)) (hd : intDet u v = 1) :
    NormedSpace.normalize (α • intVector traceBasis u + β • intVector traceBasis v) ∈
      traceBoundaryOpenArc (traceRationalParameter k u) (traceRationalParameter k v) := by
  let s := positiveCombinationQuarterParameter k u v α β
  have hs : s ∈ Ioo (traceRationalQuarterParameter k u) (traceRationalQuarterParameter k v) :=
    positiveCombinationQuarterParameter_mem_Ioo k u v α β hα hβ hu hv hd
  have hsu := traceRationalQuarterParameter_mem_Icc k u hu0 hu1 hu
  have hsv := traceRationalQuarterParameter_mem_Icc k v hv0 hv1 hv
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hsu.1.trans hs.1.le, hs.2.le.trans hsv.2⟩
  refine ⟨(k.val : ℝ) + s, ?_, ?_⟩
  · constructor <;> dsimp [traceRationalParameter] <;> linarith [hs.1, hs.2]
  · rw [traceBoundaryPath_add_eq_chordBoundarySection k s hsI]
    exact chordBoundarySection_positiveCombinationQuarterParameter k u v α β hα hβ hu hv

/-- Positive combinations of actual seeded Farey labels lie on the
corresponding actual open trace-boundary arc. -/
theorem SeededFarey.normalize_positiveCombination_mem_traceBoundaryOpenArc
    {k : Fin 4} {u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      M0 N0 u v M N) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    NormedSpace.normalize (α • intVector traceBasis u + β • intVector traceBasis v) ∈
      traceBoundaryOpenArc (traceRationalParameter k u) (traceRationalParameter k v) := by
  have hu := h.quadrant_left_nonnegativePrimitive
  have hv := h.quadrant_right_nonnegativePrimitive
  exact Markov.normalize_positiveCombination_mem_traceBoundaryOpenArc k u v α β hα hβ
    hu.1 hu.2.1 hv.1 hv.2.1 (profileMass_pos _ hu) (profileMass_pos _ hv)
    (h.det_eq_seed.trans (quadrantSeed_det_eq_one k))

end Markov
