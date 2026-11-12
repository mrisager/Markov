import Markov.GlobalCutoffCoverage

/-! Every actual cutoff component of the constructed trace unit boundary
has the uniform Euclidean curve-variation bound at the primitive endpoint
height scale. The curve is measured in the fixed original Euclidean
coordinates. No identification with a hyperbolic surface is used. -/

noncomputable section
open scoped NNReal ENNReal
namespace Markov

/-- Undoing the signed coordinate change preserves actual cutoff membership. -/
theorem inverse_signedSectorCoordinates_mem_primitiveDirectionsUpTo
    (k : Fin 8) (H : ℕ) (u : ℤ × ℤ) (hu : u ∈ cutoffSlopesUpTo H) :
    signedSectorCoordinates (signedSectorInverse k) u ∈ primitiveDirectionsUpTo H := by
  exact (signedSectorCoordinates_mem_primitiveDirectionsUpTo _ H u).mpr
    (cutoffSlope_mem_primitiveDirectionsUpTo H u hu)

/-- The original endpoint's infinity height is exactly its positive
canonical denominator, rather than the norm of a reflected source vector. -/
theorem inverse_signedSectorCoordinates_intHeight_eq_first
    (k : Fin 8) (H : ℕ) (u : ℤ × ℤ) (hu : u ∈ cutoffSlopesUpTo H) :
    intHeight (signedSectorCoordinates (signedSectorInverse k) u) = (u.1 : ℝ) := by
  obtain ⟨hp, hq, hqp, _, _⟩ := (mem_cutoffSlopesUpTo H u).mp hu
  have hp' : (0 : ℝ) ≤ u.1 := by exact_mod_cast hp.le
  have hq' : (0 : ℝ) ≤ u.2 := by exact_mod_cast hq
  have hqp' : (u.2 : ℝ) ≤ u.1 := by exact_mod_cast hqp
  rw [signedSectorCoordinates_height, intHeight, abs_of_nonneg hp',
    abs_of_nonneg hq', max_eq_left hqp']

/-- The signed radial endpoint is the normalized original primitive
direction in the original normed plane. -/
theorem signedSectorBasis_radial_cutoff_endpoint {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Module.Basis (Fin 2) ℝ E) (k : Fin 8) (u : ℤ × ℤ) (hu : 0 < u.1) :
    radialBasisSection (signedSectorBasis B k) (cutoffSlope u) =
      NormedSpace.normalize
        (intVector B (signedSectorCoordinates (signedSectorInverse k) u)) := by
  have hinv : signedSectorCoordinates k
      (signedSectorCoordinates (signedSectorInverse k) u) = u := by
    simpa only [signedSectorInverse_involutive] using
      signedSectorCoordinates_inverse (signedSectorInverse k) u
  have he := signedSectorBasis_intVector B k
    (signedSectorCoordinates (signedSectorInverse k) u)
  rw [hinv] at he
  rw [← normalize_intVector_eq_radialBasisSection _ u hu]
  exact congrArg NormedSpace.normalize he

/-- The endpoint identity remains exact in the fixed Euclidean coordinates. -/
theorem signedTraceEuclideanRadialSection_original_cutoff_endpoint
    (k : Fin 8) (u : ℤ × ℤ) (hu : 0 < u.1) :
    signedTraceEuclideanRadialSection k (cutoffSlope u) =
      traceEuclideanCoordinates (NormedSpace.normalize
        (intVector traceBasis (signedSectorCoordinates (signedSectorInverse k) u))) := by
  exact congrArg traceEuclideanCoordinates
    (signedSectorBasis_radial_cutoff_endpoint traceBasis k u hu)

/-- Euclidean variation of the closed endpoint parametrization of an
actual signed cutoff arc. -/
def signedTraceCutoffArcLength (k : Fin 8) (u v : ℤ × ℤ) : ℝ≥0∞ :=
  eVariationOn (signedTraceEuclideanRadialSection k)
    (Set.Icc (cutoffSlope u) (cutoffSlope v))

/-- Actual cutoff consecutiveness gives the uniform length scale in the
original primitive endpoint heights. -/
theorem signedTraceCutoffArcLength_le_original_heights
    (k : Fin 8) (H : ℕ) (u v : ℤ × ℤ) (h : ConsecutiveCutoffSlopes H u v) :
    signedTraceCutoffArcLength k u v ≤
      ENNReal.ofReal (2 * (signedTraceEuclideanArcConstant : ℝ) /
        ((H : ℝ) * min
          (intHeight (signedSectorCoordinates (signedSectorInverse k) u))
          (intHeight (signedSectorCoordinates (signedSectorInverse k) v)))) := by
  rw [inverse_signedSectorCoordinates_intHeight_eq_first k H u h.1,
    inverse_signedSectorCoordinates_intHeight_eq_first k H v h.2.1]
  exact signedTraceEuclideanRadialSection_cutoff_eVariationOn_le k H u v h

/-- The same actual Euclidean length bound as a real-valued estimate. -/
theorem signedTraceCutoffArcLength_toReal_le_original_heights
    (k : Fin 8) (H : ℕ) (u v : ℤ × ℤ) (h : ConsecutiveCutoffSlopes H u v) :
    (signedTraceCutoffArcLength k u v).toReal ≤
      2 * (signedTraceEuclideanArcConstant : ℝ) /
        ((H : ℝ) * min
          (intHeight (signedSectorCoordinates (signedSectorInverse k) u))
          (intHeight (signedSectorCoordinates (signedSectorInverse k) v))) := by
  rw [inverse_signedSectorCoordinates_intHeight_eq_first k H u h.1,
    inverse_signedSectorCoordinates_intHeight_eq_first k H v h.2.1]
  have hb := signedTraceEuclideanRadialSection_cutoff_eVariationOn_le k H u v h
  have hup : (0 : ℝ) < u.1 := by
    exact_mod_cast ((mem_cutoffSlopesUpTo H u).mp h.1).1
  have hvp : (0 : ℝ) < v.1 := by
    exact_mod_cast ((mem_cutoffSlopesUpTo H v).mp h.2.1).1
  exact (ENNReal.toReal_mono (by finiteness) hb).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

/-- One strictly positive real constant works for every signed component
and every positive primitive cutoff. -/
def traceGlobalCutoffArcLengthConstant : ℝ :=
  2 * (signedTraceEuclideanArcConstant : ℝ) + 1

theorem traceGlobalCutoffArcLengthConstant_pos : 0 < traceGlobalCutoffArcLengthConstant := by
  dsimp [traceGlobalCutoffArcLengthConstant]
  positivity

theorem signedTraceCutoffArcLength_le_uniform_constant
    (k : Fin 8) (H : ℕ) (u v : ℤ × ℤ) (h : ConsecutiveCutoffSlopes H u v) :
    signedTraceCutoffArcLength k u v ≤
      ENNReal.ofReal (traceGlobalCutoffArcLengthConstant /
        ((H : ℝ) * min
          (intHeight (signedSectorCoordinates (signedSectorInverse k) u))
          (intHeight (signedSectorCoordinates (signedSectorInverse k) v)))) := by
  rw [inverse_signedSectorCoordinates_intHeight_eq_first k H u h.1,
    inverse_signedSectorCoordinates_intHeight_eq_first k H v h.2.1]
  apply (signedTraceEuclideanRadialSection_cutoff_eVariationOn_le k H u v h).trans
  apply ENNReal.ofReal_le_ofReal
  have hu0 : (0 : ℝ) ≤ u.1 := by
    exact_mod_cast ((mem_cutoffSlopesUpTo H u).mp h.1).1.le
  have hv0 : (0 : ℝ) ≤ v.1 := by
    exact_mod_cast ((mem_cutoffSlopesUpTo H v).mp h.2.1).1.le
  exact div_le_div_of_nonneg_right
    (by dsimp [traceGlobalCutoffArcLengthConstant]; linarith)
    (mul_nonneg (Nat.cast_nonneg H) (le_min hu0 hv0))

/-- Every unit-boundary point outside the actual primitive cutoff has a
true connected component, actual primitive endpoint labels, exact endpoint
parametrizations, and the Euclidean curve-length scale in original heights. -/
theorem trace_uncut_boundary_exists_signed_component_variation_le
    (H : ℕ) (hH : 1 ≤ H) (x : TracePlane)
    (hx : x ∈ frontier (Metric.closedBall (0 : TracePlane) 1) \
      (↑(cutoffCorners traceBasis H) : Set TracePlane)) :
    ∃ (k : Fin 8) (u v : ℤ × ℤ), ConsecutiveCutoffSlopes H u v ∧
      x ∈ slopeBoundaryArc (signedSectorBasis traceBasis k)
        (cutoffSlope u) (cutoffSlope v) ∧
      connectedComponentIn
        (frontier (Metric.closedBall (0 : TracePlane) 1) \
          (↑(cutoffCorners traceBasis H) : Set TracePlane)) x =
        slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) ∧
      signedSectorCoordinates (signedSectorInverse k) u ∈ primitiveDirectionsUpTo H ∧
      signedSectorCoordinates (signedSectorInverse k) v ∈ primitiveDirectionsUpTo H ∧
      signedTraceEuclideanRadialSection k (cutoffSlope u) =
        traceEuclideanCoordinates (NormedSpace.normalize
          (intVector traceBasis (signedSectorCoordinates (signedSectorInverse k) u))) ∧
      signedTraceEuclideanRadialSection k (cutoffSlope v) =
        traceEuclideanCoordinates (NormedSpace.normalize
          (intVector traceBasis (signedSectorCoordinates (signedSectorInverse k) v))) ∧
      signedTraceCutoffArcLength k u v ≤
        ENNReal.ofReal (2 * (signedTraceEuclideanArcConstant : ℝ) /
          ((H : ℝ) * min
            (intHeight (signedSectorCoordinates (signedSectorInverse k) u))
            (intHeight (signedSectorCoordinates (signedSectorInverse k) v)))) := by
  obtain ⟨k, u, v, h, hxarc, hcomponent⟩ :=
    uncut_boundary_exists_signed_cutoff_component traceBasis H hH x hx
  exact ⟨k, u, v, h, hxarc, hcomponent,
    inverse_signedSectorCoordinates_mem_primitiveDirectionsUpTo k H u h.1,
    inverse_signedSectorCoordinates_mem_primitiveDirectionsUpTo k H v h.2.1,
    signedTraceEuclideanRadialSection_original_cutoff_endpoint k u
      ((mem_cutoffSlopesUpTo H u).mp h.1).1,
    signedTraceEuclideanRadialSection_original_cutoff_endpoint k v
      ((mem_cutoffSlopesUpTo H v).mp h.2.1).1,
    signedTraceCutoffArcLength_le_original_heights k H u v h⟩

/-- A positive real constant bounds the actual Euclidean parametrization
length of the component containing every uncut unit-boundary point. -/
theorem trace_uncut_boundary_exists_uniform_component_length_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℕ), 1 ≤ H → ∀ (x : TracePlane),
      x ∈ frontier (Metric.closedBall (0 : TracePlane) 1) \
        (↑(cutoffCorners traceBasis H) : Set TracePlane) →
      ∃ (k : Fin 8) (u v : ℤ × ℤ), ConsecutiveCutoffSlopes H u v ∧
        connectedComponentIn
          (frontier (Metric.closedBall (0 : TracePlane) 1) \
            (↑(cutoffCorners traceBasis H) : Set TracePlane)) x =
          slopeBoundaryArc (signedSectorBasis traceBasis k) (cutoffSlope u) (cutoffSlope v) ∧
        signedTraceCutoffArcLength k u v ≤ ENNReal.ofReal (C /
          ((H : ℝ) * min
            (intHeight (signedSectorCoordinates (signedSectorInverse k) u))
            (intHeight (signedSectorCoordinates (signedSectorInverse k) v)))) := by
  refine ⟨traceGlobalCutoffArcLengthConstant, traceGlobalCutoffArcLengthConstant_pos, ?_⟩
  intro H hH x hx
  obtain ⟨k, u, v, h, _, hcomponent⟩ :=
    uncut_boundary_exists_signed_cutoff_component traceBasis H hH x hx
  exact ⟨k, u, v, h, hcomponent,
    signedTraceCutoffArcLength_le_uniform_constant k H u v h⟩

end Markov
