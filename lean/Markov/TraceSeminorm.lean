import Markov.SeedLinearPieces
import Markov.ActualAxisJoins
import Markov.NormLimit

/-! Concrete signed-support seminorms for the modular trace data. All
quadrant gluing hypotheses are discharged by the checked seed profiles and
actual axis inequalities; no norm-existence assumption is made. -/

noncomputable section
namespace Markov

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def traceAxisLength : ℝ := 2 * Real.arcosh ((3 : ℝ) / 2)

theorem traceAxisLength_pos : 0 < traceAxisLength := by
  exact mul_pos (by norm_num) (Real.arcosh_pos (by norm_num))

def quarterCoordinateMap (B : Module.Basis (Fin 2) ℝ E) : E →ₗ[ℝ] E :=
  (B.coord 1).smulRight (B 0) - (B.coord 0).smulRight (B 1)

@[simp] theorem quarterCoordinateMap_zero (B : Module.Basis (Fin 2) ℝ E) :
    quarterCoordinateMap B (B 0) = -(B 1) := by
  simp [quarterCoordinateMap, Module.Basis.coord_apply, Module.Basis.repr_self]

@[simp] theorem quarterCoordinateMap_one (B : Module.Basis (Fin 2) ℝ E) :
    quarterCoordinateMap B (B 1) = B 0 := by
  simp [quarterCoordinateMap, Module.Basis.coord_apply, Module.Basis.repr_self]

def positiveTracePiece (B : Module.Basis (Fin 2) ℝ E) (n i : ℕ) : E →ₗ[ℝ] ℝ :=
  seedLinearPiece B modularGeneratorA modularGeneratorB n i

def mixedTracePiece (B : Module.Basis (Fin 2) ℝ E) (n i : ℕ) : E →ₗ[ℝ] ℝ :=
  (seedLinearPiece B modularGeneratorB modularGeneratorA.adjugate n i).comp (quarterCoordinateMap B)

@[simp] theorem mixedTracePiece_zero (B : Module.Basis (Fin 2) ℝ E) (n i : ℕ) :
    mixedTracePiece B n i (B 0) = -(seedFrontierOffsets modularGeneratorB modularGeneratorA.adjugate n i +
      seedFrontierSlopes modularGeneratorB modularGeneratorA.adjugate n i) := by
  simp only [mixedTracePiece, LinearMap.comp_apply, quarterCoordinateMap_zero, map_neg,
    seedLinearPiece_apply_basis_one]

@[simp] theorem mixedTracePiece_one (B : Module.Basis (Fin 2) ℝ E) (n i : ℕ) :
    mixedTracePiece B n i (B 1) = seedFrontierOffsets modularGeneratorB modularGeneratorA.adjugate n i := by
  simp only [mixedTracePiece, LinearMap.comp_apply, quarterCoordinateMap_one,
    seedLinearPiece_apply_basis_zero]

def finiteTraceSeminorm (B : Module.Basis (Fin 2) ℝ E) (n : ℕ) : Seminorm ℝ E :=
  signedLinearSeminorm (positiveTracePiece B n) (mixedTracePiece B n) (2 ^ n - 1) (2 ^ n - 1)

theorem positiveTracePiece_first_zero (B : Module.Basis (Fin 2) ℝ E) (n : ℕ) :
    positiveTracePiece B n 0 (B 0) = traceAxisLength := by
  simp only [positiveTracePiece, seedLinearPiece_apply_basis_zero, seedFrontierOffsets,
    seedEdgeOffset_first_axis, modular_generators_det_trace.2.2.1, Int.cast_ofNat, traceAxisLength]

theorem positiveTracePiece_last_one (B : Module.Basis (Fin 2) ℝ E) (n : ℕ) :
    positiveTracePiece B n (2 ^ n - 1) (B 1) = traceAxisLength := by
  simp only [positiveTracePiece, seedLinearPiece_apply_basis_one, seedFrontierOffsets,
    seedFrontierSlopes, seedEdgeOffset_add_slope_last_axis,
    modular_generators_det_trace.2.2.2.1, Int.cast_ofNat, traceAxisLength]

theorem mixedTracePiece_first_one (B : Module.Basis (Fin 2) ℝ E) (n : ℕ) :
    mixedTracePiece B n 0 (B 1) = traceAxisLength := by
  simp only [mixedTracePiece_one, seedFrontierOffsets, seedEdgeOffset_first_axis,
    modular_generators_det_trace.2.2.2.1, Int.cast_ofNat, traceAxisLength]

theorem mixedTracePiece_last_zero (B : Module.Basis (Fin 2) ℝ E) (n : ℕ) :
    mixedTracePiece B n (2 ^ n - 1) (B 0) = -traceAxisLength := by
  simp only [mixedTracePiece_zero, seedFrontierOffsets, seedFrontierSlopes,
    seedEdgeOffset_add_slope_last_axis, matrix_two_trace_adjugate,
    modular_generators_det_trace.2.2.1, Int.cast_ofNat, traceAxisLength]

theorem mixedTracePiece_zero_bounds (B : Module.Basis (Fin 2) ℝ E) (n i : ℕ)
    (hi : i ≤ 2 ^ n - 1) :
    mixedTracePiece B n (2 ^ n - 1) (B 0) ≤ mixedTracePiece B n i (B 0) ∧
      mixedTracePiece B n i (B 0) ≤ mixedTracePiece B n 0 (B 0) := by
  have h := seedLinearPiece_basis_one_bounds B modularGeneratorB modularGeneratorA.adjugate
    (quadrantSeed_positiveFrickePair 1) n i hi
  simp only [seedLinearPiece_apply_basis_one] at h
  simp only [mixedTracePiece_zero]
  constructor <;> linarith [h.1, h.2]

theorem mixedTracePiece_one_bounds (B : Module.Basis (Fin 2) ℝ E) (n i : ℕ)
    (hi : i ≤ 2 ^ n - 1) :
    mixedTracePiece B n (2 ^ n - 1) (B 1) ≤ mixedTracePiece B n i (B 1) ∧
      mixedTracePiece B n i (B 1) ≤ mixedTracePiece B n 0 (B 1) := by
  simpa only [mixedTracePiece_one, seedLinearPiece_apply_basis_zero] using
    seedLinearPiece_basis_zero_bounds B modularGeneratorB modularGeneratorA.adjugate
      (quadrantSeed_positiveFrickePair 1) n i hi

theorem quarterCoordinateMap_next_cone (B : Module.Basis (Fin 2) ℝ E) (x : E)
    (hx : x ∈ twoRayCone (B 1) (-B 0)) : quarterCoordinateMap B x ∈ twoRayCone (B 0) (B 1) := by
  obtain ⟨s, t, hs, ht, rfl⟩ := hx
  refine ⟨s, t, hs, ht, ?_⟩
  simp only [map_add, map_smul, map_neg, quarterCoordinateMap_one, quarterCoordinateMap_zero, neg_neg]

theorem mixedTracePiece_min_on_cone (B : Module.Basis (Fin 2) ℝ E) (n : ℕ) (x : E)
    (hx : x ∈ twoRayCone (B 1) (-B 0)) (i : ℕ) (hi : i ≤ 2 ^ n - 1) :
    min (mixedTracePiece B n 0 x) (mixedTracePiece B n (2 ^ n - 1) x) ≤ mixedTracePiece B n i x := by
  exact seedLinearPiece_min_on_cone B modularGeneratorB modularGeneratorA.adjugate
    (quadrantSeed_positiveFrickePair 1) n (quarterCoordinateMap B x)
    (quarterCoordinateMap_next_cone B x hx) i hi

/-- Concrete interpolation on the first quadrant by the actual seminorm. -/
theorem finiteTraceSeminorm_positive_cone (B : Module.Basis (Fin 2) ℝ E) (n : ℕ) (x : E)
    (hx : x ∈ twoRayCone (B 0) (B 1)) :
    finiteTraceSeminorm B n x = prefixEnvelope (fun i => (positiveTracePiece B n i : E → ℝ)) (2 ^ n - 1) x := by
  apply signedLinearSeminorm_eq_on_quadrant (positiveTracePiece B n) (mixedTracePiece B n)
    (2 ^ n - 1) (2 ^ n - 1) (B 0) (B 1) traceAxisLength
    (positiveTracePiece_first_zero B n) (positiveTracePiece_last_one B n)
    (mixedTracePiece_first_one B n) (mixedTracePiece_last_zero B n)
    (mixedTracePiece_zero_bounds B n) (mixedTracePiece_one_bounds B n)
  · simpa only [mixedTracePiece_zero, positiveTracePiece, seedLinearPiece_apply_basis_zero]
      using actual_axis_join_zero n
  · simpa only [positiveTracePiece, seedLinearPiece_apply_basis_one, mixedTracePiece_one]
      using actual_axis_join_one n
  · exact fun x hx i hi => seedLinearPiece_min_on_cone B modularGeneratorA modularGeneratorB
      seed_positiveFrickePair n x hx i hi
  · exact hx

/-- Concrete interpolation on the next quadrant. Evenness supplies its opposite. -/
theorem finiteTraceSeminorm_next_cone (B : Module.Basis (Fin 2) ℝ E) (n : ℕ) (x : E)
    (hx : x ∈ twoRayCone (B 1) (-B 0)) :
    finiteTraceSeminorm B n x = prefixEnvelope (fun i => (mixedTracePiece B n i : E → ℝ)) (2 ^ n - 1) x := by
  apply signedLinearSeminorm_eq_on_next_quadrant (positiveTracePiece B n) (mixedTracePiece B n)
    (2 ^ n - 1) (2 ^ n - 1) (B 0) (B 1) traceAxisLength
    (positiveTracePiece_first_zero B n) (positiveTracePiece_last_one B n)
    (mixedTracePiece_first_one B n) (mixedTracePiece_last_zero B n)
  · exact seedLinearPiece_basis_zero_bounds B modularGeneratorA modularGeneratorB seed_positiveFrickePair n
  · exact seedLinearPiece_basis_one_bounds B modularGeneratorA modularGeneratorB seed_positiveFrickePair n
  · simpa only [mixedTracePiece_zero, positiveTracePiece, seedLinearPiece_apply_basis_zero]
      using actual_axis_join_zero n
  · simpa only [positiveTracePiece, seedLinearPiece_apply_basis_one, mixedTracePiece_one]
      using actual_axis_join_one n
  · exact mixedTracePiece_min_on_cone B n
  · exact hx

end Markov
