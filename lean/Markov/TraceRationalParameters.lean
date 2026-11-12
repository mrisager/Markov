import Markov.TraceBoundaryInjective
import Markov.SeededCoordinates
import Markov.FareyProfile

/-! Rational parameters for actual integer directions on the trace boundary.
The coordinate ratios are taken in the actual quadrant frames; the only
normalization used below is that of the constructed trace norm. -/

noncomputable section
open Set

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalizing a basis chord at its coordinate ratio recovers the original
ray, including either coordinate-axis endpoint. -/
theorem chordBoundarySection_ratio_eq_normalize
    (B : Module.Basis (Fin 2) ℝ E) (a b : ℝ) (hsum : 0 < a + b) :
    chordBoundarySection B (b / (a + b)) =
      NormedSpace.normalize (a • B 0 + b • B 1) := by
  have hcoef : 1 - b / (a + b) = (a + b)⁻¹ * a := by
    field_simp [ne_of_gt hsum]
    ring
  have he : (1 - b / (a + b)) • B 0 + (b / (a + b)) • B 1 =
      (a + b)⁻¹ • (a • B 0 + b • B 1) := by
    rw [smul_add, smul_smul, smul_smul, hcoef]
    simp only [div_eq_mul_inv, mul_comm]
  rw [chordBoundarySection_eq_normalize, he,
    NormedSpace.normalize_smul_of_pos (inv_pos.mpr hsum)]

/-- Actual integer coordinates reconstruct the same real vector in the
corresponding quarter-turn basis. No norm symmetry is involved. -/
theorem traceRotationBasis_quadrantCoordinates (k : Fin 4) (p : ℤ × ℤ) :
    ((quadrantCoordinates k p).1 : ℝ) • traceRotationBasis k.val 0 +
      ((quadrantCoordinates k p).2 : ℝ) • traceRotationBasis k.val 1 =
        intVector traceBasis p := by
  fin_cases k <;>
    simp only [quadrantCoordinates, traceRotationBasis, Function.iterate_succ_apply,
      Function.iterate_zero_apply, quarterTurnBasis_zero, quarterTurnBasis_one,
      Int.cast_neg, intVector] <;> module

/-- The local chord parameter of an integer direction in its quadrant. -/
def traceRationalQuarterParameter (k : Fin 4) (p : ℤ × ℤ) : ℝ :=
  profileParameter (quadrantCoordinates k p)

/-- The actual four-chord path parameter of an integer direction. -/
def traceRationalParameter (k : Fin 4) (p : ℤ × ℤ) : ℝ :=
  (k.val : ℝ) + traceRationalQuarterParameter k p

theorem traceRationalQuarterParameter_mem_Icc (k : Fin 4) (p : ℤ × ℤ)
    (h0 : 0 ≤ (quadrantCoordinates k p).1)
    (h1 : 0 ≤ (quadrantCoordinates k p).2)
    (hsum : 0 < profileMass (quadrantCoordinates k p)) :
    traceRationalQuarterParameter k p ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (by exact_mod_cast h1) hsum.le
  · apply (div_le_one hsum).mpr
    have h0R : (0 : ℝ) ≤ (quadrantCoordinates k p).1 := by exact_mod_cast h0
    dsimp [profileMass]
    linarith

/-- The local rational parameter lies in its closed quarter, so both axis
seams of every quarter are allowed. -/
theorem traceRationalParameter_mem_quarter (k : Fin 4) (p : ℤ × ℤ)
    (h0 : 0 ≤ (quadrantCoordinates k p).1)
    (h1 : 0 ≤ (quadrantCoordinates k p).2)
    (hsum : 0 < profileMass (quadrantCoordinates k p)) :
    traceRationalParameter k p ∈ Icc (k.val : ℝ) ((k.val : ℝ) + 1) := by
  have hs := traceRationalQuarterParameter_mem_Icc k p h0 h1 hsum
  constructor <;> dsimp [traceRationalParameter] <;> linarith [hs.1, hs.2]

/-- The rational chord parameter reaches exactly the normalized actual
integer vector, including the coordinate axes. -/
theorem chordBoundarySection_traceRationalQuarterParameter
    (k : Fin 4) (p : ℤ × ℤ)
    (hsum : 0 < profileMass (quadrantCoordinates k p)) :
    chordBoundarySection (traceRotationBasis k.val) (traceRationalQuarterParameter k p) =
      NormedSpace.normalize (intVector traceBasis p) := by
  change chordBoundarySection (traceRotationBasis k.val)
    (((quadrantCoordinates k p).2 : ℝ) /
      (((quadrantCoordinates k p).1 : ℝ) + ((quadrantCoordinates k p).2 : ℝ))) = _
  rw [chordBoundarySection_ratio_eq_normalize _ _ _ hsum,
    traceRotationBasis_quadrantCoordinates]

/-- The actual global path reaches a nonnegative quadrant direction at its
rational parameter. The closed-interval path identity handles all seams. -/
theorem traceBoundaryPath_traceRationalParameter (k : Fin 4) (p : ℤ × ℤ)
    (h0 : 0 ≤ (quadrantCoordinates k p).1)
    (h1 : 0 ≤ (quadrantCoordinates k p).2)
    (hsum : 0 < profileMass (quadrantCoordinates k p)) :
    traceBoundaryPath (traceRationalParameter k p) =
      NormedSpace.normalize (intVector traceBasis p) := by
  rw [traceRationalParameter,
    traceBoundaryPath_add_eq_chordBoundarySection k _
      (traceRationalQuarterParameter_mem_Icc k p h0 h1 hsum)]
  exact chordBoundarySection_traceRationalQuarterParameter k p hsum

/-- Positive determinant orders coordinate ratios whenever their two
coordinate masses are positive. -/
theorem traceRationalQuarterParameter_lt_of_det_one (k : Fin 4) (u v : ℤ × ℤ)
    (hu : 0 < profileMass (quadrantCoordinates k u))
    (hv : 0 < profileMass (quadrantCoordinates k v)) (hd : intDet u v = 1) :
    traceRationalQuarterParameter k u < traceRationalQuarterParameter k v := by
  apply (div_lt_div_iff₀ hu hv).mpr
  have hc : intDet (quadrantCoordinates k u) (quadrantCoordinates k v) = 1 := by
    rw [quadrantCoordinates_det, hd]
  have hdR : ((quadrantCoordinates k u).1 : ℝ) * ((quadrantCoordinates k v).2 : ℝ) -
      ((quadrantCoordinates k u).2 : ℝ) * ((quadrantCoordinates k v).1 : ℝ) = 1 := by
    exact_mod_cast hc
  dsimp [profileMass]
  nlinarith

theorem traceRationalParameter_lt_of_det_one (k : Fin 4) (u v : ℤ × ℤ)
    (hu : 0 < profileMass (quadrantCoordinates k u))
    (hv : 0 < profileMass (quadrantCoordinates k v)) (hd : intDet u v = 1) :
    traceRationalParameter k u < traceRationalParameter k v := by
  dsimp [traceRationalParameter]
  linarith [traceRationalQuarterParameter_lt_of_det_one k u v hu hv hd]

namespace SeededFarey

variable {k : Fin 4} {u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
variable (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
  M0 N0 u v M N)
include h

/-- Each first seeded label has a valid closed-quarter rational parameter. -/
theorem traceRationalQuarterParameter_left_mem_Icc :
    traceRationalQuarterParameter k u ∈ Icc (0 : ℝ) 1 := by
  have hu := h.quadrant_left_nonnegativePrimitive
  exact traceRationalQuarterParameter_mem_Icc k u hu.1 hu.2.1 (profileMass_pos _ hu)

/-- Each second seeded label has a valid closed-quarter rational parameter. -/
theorem traceRationalQuarterParameter_right_mem_Icc :
    traceRationalQuarterParameter k v ∈ Icc (0 : ℝ) 1 := by
  have hv := h.quadrant_right_nonnegativePrimitive
  exact traceRationalQuarterParameter_mem_Icc k v hv.1 hv.2.1 (profileMass_pos _ hv)

theorem traceBoundaryPath_traceRationalParameter_left :
    traceBoundaryPath (traceRationalParameter k u) =
      NormedSpace.normalize (intVector traceBasis u) := by
  have hu := h.quadrant_left_nonnegativePrimitive
  exact Markov.traceBoundaryPath_traceRationalParameter k u hu.1 hu.2.1
    (profileMass_pos _ hu)

theorem traceBoundaryPath_traceRationalParameter_right :
    traceBoundaryPath (traceRationalParameter k v) =
      NormedSpace.normalize (intVector traceBasis v) := by
  have hv := h.quadrant_right_nonnegativePrimitive
  exact Markov.traceBoundaryPath_traceRationalParameter k v hv.1 hv.2.1
    (profileMass_pos _ hv)

/-- The actual seeded Farey orientation strictly orders its local rational
parameters, even when an endpoint lies on an axis. -/
theorem traceRationalQuarterParameter_lt :
    traceRationalQuarterParameter k u < traceRationalQuarterParameter k v := by
  apply traceRationalQuarterParameter_lt_of_det_one k u v
    (profileMass_pos _ h.quadrant_left_nonnegativePrimitive)
    (profileMass_pos _ h.quadrant_right_nonnegativePrimitive)
  exact h.det_eq_seed.trans (quadrantSeed_det_eq_one k)

/-- A seeded Farey pair occurs in strict order on the actual path. -/
theorem traceRationalParameter_lt :
    traceRationalParameter k u < traceRationalParameter k v := by
  dsimp [traceRationalParameter]
  linarith [h.traceRationalQuarterParameter_lt]

end SeededFarey
end Markov
