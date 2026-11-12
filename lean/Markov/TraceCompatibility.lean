import Markov.SeededSeparation
import Markov.QuadrantSymmetry
import Markov.SeededCoordinates
import Markov.TracePlane

/-! Trace compatibility in opposite quadrants follows from the antipodal
matrix transport and norm symmetry. Only the first two quadrants require
independent interpolation calculations. -/

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem intVector_neg_direction (B : Module.Basis (Fin 2) ℝ E)
    (p : ℤ × ℤ) : intVector B (-p) = -intVector B p := by
  simp only [intVector, Prod.fst_neg, Prod.snd_neg, Int.cast_neg, neg_smul, neg_add]

/-- Antipodal matrix transport carries trace compatibility to the opposite
quadrant, because the norm is unchanged by central negation. -/
theorem SeededTraceLengthCompatible.antipodal_quadrant
    (B : Module.Basis (Fin 2) ℝ E) (k : Fin 4)
    (hk : SeededTraceLengthCompatible B
      (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2) :
    SeededTraceLengthCompatible B
      (quadrantSeedDirections (antipodalQuadrant k)).1
      (quadrantSeedDirections (antipodalQuadrant k)).2
      (quadrantSeedMatrices (antipodalQuadrant k)).1
      (quadrantSeedMatrices (antipodalQuadrant k)).2 := by
  intro u v M N h
  have hneg := h.quadrant_antipodal (antipodalQuadrant k)
  rw [antipodalQuadrant_involutive] at hneg
  have hh := hk hneg
  simpa only [antipodalMatrix_trace, intVector_neg_direction, norm_neg] using hh

/-- Compatibility on the first two quadrants determines compatibility on
all four actual matrix seeds. -/
theorem quadrantTraceLengthCompatible_of_zero_one
    (B : Module.Basis (Fin 2) ℝ E)
    (hzero : SeededTraceLengthCompatible B
      (quadrantSeedDirections 0).1 (quadrantSeedDirections 0).2
      (quadrantSeedMatrices 0).1 (quadrantSeedMatrices 0).2)
    (hone : SeededTraceLengthCompatible B
      (quadrantSeedDirections 1).1 (quadrantSeedDirections 1).2
      (quadrantSeedMatrices 1).1 (quadrantSeedMatrices 1).2) :
    QuadrantTraceLengthCompatible B := by
  intro k
  fin_cases k
  · exact hzero
  · exact hone
  · exact hzero.antipodal_quadrant B 0
  · exact hone.antipodal_quadrant B 1

/-- Primitive length interpolation in quadrant coordinates determines the
trace--length relation for every actual word in that quadrant. -/
theorem seededTraceLengthCompatible_of_quadrant_interpolation
    (B : Module.Basis (Fin 2) ℝ E) (k : Fin 4)
    (hL : ∀ (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)),
      ‖intVector B p‖ = primitiveSeedLength
        (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
        (quadrantCoordinates k p) hp) :
    SeededTraceLengthCompatible B
      (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 := by
  intro u v M N h
  have hu := h.quadrant_left_nonnegativePrimitive
  have hv := h.quadrant_right_nonnegativePrimitive
  constructor
  · rw [hL u hu]
    have hh := primitiveSeedTrace_eq_two_cosh _ _ (quadrantSeed_positiveFrickePair k)
      (quadrantCoordinates k u) hu
    simpa only [primitiveSeedTrace, h.quadrant_primitiveSeedMatrix_left hu] using hh
  · rw [hL v hv]
    have hh := primitiveSeedTrace_eq_two_cosh _ _ (quadrantSeed_positiveFrickePair k)
      (quadrantCoordinates k v) hv
    simpa only [primitiveSeedTrace, h.quadrant_primitiveSeedMatrix_right hv] using hh

/-- The constructed trace norm has the trace--length relation for every
matrix word in all four concrete quadrants. -/
theorem tracePlane_quadrantTraceLengthCompatible :
    QuadrantTraceLengthCompatible traceBasis := by
  apply quadrantTraceLengthCompatible_of_zero_one traceBasis
  · apply seededTraceLengthCompatible_of_quadrant_interpolation traceBasis 0
    intro p hp
    exact norm_intVector_positive p hp
  · apply seededTraceLengthCompatible_of_quadrant_interpolation traceBasis 1
    intro p hp
    exact norm_intVector_quadrant_one p hp

end Markov
