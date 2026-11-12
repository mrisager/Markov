import Markov.HyperbolicDiagonalization
import Markov.SeededCoordinates

/-! Metric lengths of the actual canonical primitive matrix words.

The canonical seeded integer matrix is bundled as an actual element of
SL(2,Z), then acts on the genuine hyperbolic upper half-plane. Its metric
translation length equals the previously constructed numerical seed length.
This is a matrix-word statement: it does not classify simple curves, identify
a homology basis, or identify a geometric stable norm. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- The actual canonical primitive seed word, with its proved determinant
one property bundled in SL(2,Z). -/
def primitiveSeedHolonomy (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) : SL(2, ℤ) :=
  ⟨primitiveSeedMatrix M0 N0 p hp, primitiveSeedMatrix_det M0 N0 h0 p hp⟩

@[simp] theorem primitiveSeedHolonomy_coe
    (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    (primitiveSeedHolonomy M0 N0 h0 p hp : IntMatrixTwo) = primitiveSeedMatrix M0 N0 p hp :=
  rfl

/-- Passing the actual canonical word from integer to real matrices
preserves its primitive trace. -/
theorem primitiveSeedHolonomy_real_trace
    (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    ((primitiveSeedHolonomy M0 N0 h0 p hp : SL(2, ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ).trace = (primitiveSeedTrace M0 N0 p hp : ℝ) := by
  simp [primitiveSeedHolonomy, primitiveSeedTrace, Matrix.trace, Matrix.diag_apply,
    Fin.sum_univ_two]

/-- Every actual canonical primitive seed word is a positive-trace
hyperbolic isometry of the genuine upper half-plane. -/
theorem primitiveSeedHolonomy_real_trace_gt_two
    (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    2 < ((primitiveSeedHolonomy M0 N0 h0 p hp : SL(2, ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ).trace := by
  rw [primitiveSeedHolonomy_real_trace]
  have hh : (3 : ℝ) ≤ primitiveSeedTrace M0 N0 p hp := by
    exact_mod_cast primitiveSeedTrace_ge_three M0 N0 h0 p hp
  linarith

/-- The numerical primitive seed length equals the genuine metric
translation length of that actual SL matrix word. -/
theorem primitiveSeedLength_eq_metricTranslationLength
    (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    primitiveSeedLength M0 N0 p hp =
      hyperbolicTranslationLength (primitiveSeedHolonomy M0 N0 h0 p hp : SL(2, ℝ)) := by
  have hh := primitiveSeedHolonomy_real_trace_gt_two M0 N0 h0 p hp
  rw [hyperbolicTranslationLength_trace_of_trace_gt_two _ hh, abs_of_pos (by linarith :
    0 < ((primitiveSeedHolonomy M0 N0 h0 p hp : SL(2, ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ).trace), primitiveSeedHolonomy_real_trace]
  rfl

/-- The actual metric displacement infimum of a canonical primitive word
is attained and equals the numerical primitive length. -/
theorem primitiveSeedHolonomy_metric_length_attained
    (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    ∃ z : UpperHalfPlane,
      dist z ((primitiveSeedHolonomy M0 N0 h0 p hp : SL(2, ℝ)) • z) =
        primitiveSeedLength M0 N0 p hp := by
  rw [primitiveSeedLength_eq_metricTranslationLength M0 N0 h0 p hp]
  exact hyperbolicTranslationLength_attained_of_trace_gt_two _
    (primitiveSeedHolonomy_real_trace_gt_two M0 N0 h0 p hp)

/-- An actual unit-speed hyperbolic axis is translated by the primitive
seed word through precisely the numerical primitive length. -/
theorem primitiveSeedHolonomy_metric_axis
    (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    ∃ γ : ℝ → UpperHalfPlane, Isometry γ ∧
      ∀ t : ℝ, (primitiveSeedHolonomy M0 N0 h0 p hp : SL(2, ℝ)) • γ t =
        γ (t + primitiveSeedLength M0 N0 p hp) := by
  rw [primitiveSeedLength_eq_metricTranslationLength M0 N0 h0 p hp]
  exact hyperbolicTranslationLength_axis_of_trace_gt_two _
    (primitiveSeedHolonomy_real_trace_gt_two M0 N0 h0 p hp)

/-- The same actual metric identity applies to primitive words in every
signed quadrant, using their existing exact coordinate transport. -/
theorem quadrantPrimitiveSeedLength_eq_metricTranslationLength
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) :
    primitiveSeedLength (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
      (quadrantCoordinates k p) hp =
      hyperbolicTranslationLength (primitiveSeedHolonomy
        (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
        (quadrantSeed_positiveFrickePair k) (quadrantCoordinates k p) hp : SL(2, ℝ)) :=
  primitiveSeedLength_eq_metricTranslationLength _ _ (quadrantSeed_positiveFrickePair k) _ hp

/-- The actual first matrix in a signed seeded word is exactly the
canonical integral SL word, not merely a matrix with the same trace. -/
theorem SeededFarey.quadrant_primitiveSeedHolonomy_left
    {k : Fin 4} {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N)
    (hu : NonnegativePrimitiveDirection (quadrantCoordinates k u)) :
    primitiveSeedHolonomy (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
      (quadrantSeed_positiveFrickePair k) (quadrantCoordinates k u) hu =
        (⟨M, (h.positiveFrickePair (quadrantSeed_positiveFrickePair k)).det_left⟩ : SL(2, ℤ)) :=
  Subtype.ext (h.quadrant_primitiveSeedMatrix_left hu)

/-- The same exact actual-matrix identity holds for the second signed word. -/
theorem SeededFarey.quadrant_primitiveSeedHolonomy_right
    {k : Fin 4} {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N)
    (hv : NonnegativePrimitiveDirection (quadrantCoordinates k v)) :
    primitiveSeedHolonomy (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
      (quadrantSeed_positiveFrickePair k) (quadrantCoordinates k v) hv =
        (⟨N, (h.positiveFrickePair (quadrantSeed_positiveFrickePair k)).det_right⟩ : SL(2, ℤ)) :=
  Subtype.ext (h.quadrant_primitiveSeedMatrix_right hv)

/-- Both actual signed quadrant word matrices have the genuine metric
lengths given by their existing canonical primitive numerical lengths. -/
theorem SeededFarey.quadrant_metricTranslationLengths
    {k : Fin 4} {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N) :
    hyperbolicTranslationLength (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
      (⟨M, (h.positiveFrickePair (quadrantSeed_positiveFrickePair k)).det_left⟩ : SL(2, ℤ))) =
        primitiveSeedLength (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
          (quadrantCoordinates k u) h.quadrant_left_nonnegativePrimitive ∧
    hyperbolicTranslationLength (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
      (⟨N, (h.positiveFrickePair (quadrantSeed_positiveFrickePair k)).det_right⟩ : SL(2, ℤ))) =
        primitiveSeedLength (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
          (quadrantCoordinates k v) h.quadrant_right_nonnegativePrimitive := by
  constructor
  · rw [← h.quadrant_primitiveSeedHolonomy_left h.quadrant_left_nonnegativePrimitive]
    exact (quadrantPrimitiveSeedLength_eq_metricTranslationLength k u _).symm
  · rw [← h.quadrant_primitiveSeedHolonomy_right h.quadrant_right_nonnegativePrimitive]
    exact (quadrantPrimitiveSeedLength_eq_metricTranslationLength k v _).symm

end Markov
