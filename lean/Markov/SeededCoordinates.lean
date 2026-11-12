import Markov.QuadrantCoverage
import Markov.SeedCanonical

/-! Transport the actual seeded matrix words to nonnegative coordinates in
each of the four quadrant bases. This preserves the matrix values exactly. -/

namespace Markov

/-- Quarter-turn coordinates preserve addition of integer directions. -/
theorem quadrantCoordinates_add (k : Fin 4) (u v : ℤ × ℤ) :
    quadrantCoordinates k (u + v) = quadrantCoordinates k u + quadrantCoordinates k v := by
  fin_cases k <;> ext <;> simp [quadrantCoordinates, add_comm]

/-- Each quadrant boundary pair has the two standard coordinate vectors. -/
theorem quadrantCoordinates_seed (k : Fin 4) :
    quadrantCoordinates k (quadrantSeedDirections k).1 = (1, 0) ∧
      quadrantCoordinates k (quadrantSeedDirections k).2 = (0, 1) := by
  fin_cases k <;> norm_num [quadrantCoordinates, quadrantSeedDirections]

/-- An actual quadrant word becomes a standard positive-sector word under
the quadrant coordinate map, with exactly the same two matrix values. -/
theorem SeededFarey.quadrant_coordinates {k : Fin 4} {u v : ℤ × ℤ}
    {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      M0 N0 u v M N) :
    SeededFarey (1, 0) (0, 1) M0 N0
      (quadrantCoordinates k u) (quadrantCoordinates k v) M N := by
  induction h with
  | seed =>
    simpa only [(quadrantCoordinates_seed k).1, (quadrantCoordinates_seed k).2]
      using (SeededFarey.seed (u0 := (1, 0)) (v0 := (0, 1)) (M0 := M0) (N0 := N0))
  | left _ ih => simpa only [quadrantCoordinates_add] using ih.left
  | right _ ih => simpa only [quadrantCoordinates_add] using ih.right

/-- The first label of every quadrant word is primitive and nonnegative
in that quadrant's coordinates. -/
theorem SeededFarey.quadrant_left_nonnegativePrimitive {k : Fin 4} {u v : ℤ × ℤ}
    {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      M0 N0 u v M N) : NonnegativePrimitiveDirection (quadrantCoordinates k u) :=
  h.quadrant_coordinates.coordinate_left_nonnegativePrimitive

/-- The second label has the same primitive nonnegative coordinate property. -/
theorem SeededFarey.quadrant_right_nonnegativePrimitive {k : Fin 4} {u v : ℤ × ℤ}
    {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      M0 N0 u v M N) : NonnegativePrimitiveDirection (quadrantCoordinates k v) :=
  h.quadrant_coordinates.coordinate_right_nonnegativePrimitive

/-- The canonical first coordinate matrix is the actual quadrant word matrix. -/
theorem SeededFarey.quadrant_primitiveSeedMatrix_left {k : Fin 4} {u v : ℤ × ℤ}
    {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      M0 N0 u v M N) (hu : NonnegativePrimitiveDirection (quadrantCoordinates k u)) :
    primitiveSeedMatrix M0 N0 (quadrantCoordinates k u) hu = M :=
  h.quadrant_coordinates.primitiveSeedMatrix_left hu

/-- The canonical second coordinate matrix is the actual quadrant word matrix. -/
theorem SeededFarey.quadrant_primitiveSeedMatrix_right {k : Fin 4} {u v : ℤ × ℤ}
    {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      M0 N0 u v M N) (hv : NonnegativePrimitiveDirection (quadrantCoordinates k v)) :
    primitiveSeedMatrix M0 N0 (quadrantCoordinates k v) hv = N :=
  h.quadrant_coordinates.primitiveSeedMatrix_right hv

end Markov
