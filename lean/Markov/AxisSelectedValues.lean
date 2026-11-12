import Markov.BirthSelectedValues
import Markov.BirthCornerJump
import Markov.CornerSupportDeterminant

/-! The two actual matrix rays adjoining each seed axis give different
norming supports. Their evaluations are the two conjugate trace coefficients;
their difference is the positive logarithmic corner expression at trace three. -/

noncomputable section

namespace Markov

local instance : Fact (3 ≤ (3 : ℤ)) := ⟨by norm_num⟩

private theorem trace_coefficient_embedding_congr {t s : ℤ}
    [Fact (3 ≤ t)] [Fact (3 ≤ s)] (h : t = s) (b c : ℤ) :
    traceRealEmbedding t (traceCoefficient t b c) =
      traceRealEmbedding s (traceCoefficient s b c) := by
  subst s
  rfl

/-- The quadrant immediately before a seed axis in counterclockwise order. -/
def axisPreviousQuadrant (k : Fin 4) : Fin 4 :=
  ⟨(k.val + 3) % 4, Nat.mod_lt _ (by decide)⟩

/-- The preceding quadrant approaches the same axis from its opposite side. -/
theorem quadrantSeedDirections_axis_previous (k : Fin 4) :
    (quadrantSeedDirections (axisPreviousQuadrant k)).1 =
        -(quadrantSeedDirections k).2 ∧
      (quadrantSeedDirections (axisPreviousQuadrant k)).2 =
        (quadrantSeedDirections k).1 := by
  fin_cases k <;> norm_num [axisPreviousQuadrant, quadrantSeedDirections]

/-- The actual product traces on the two sides of an axis are conjugate
Fricke partners: three and six, in the order determined by the quadrant. -/
theorem quadrantSeed_product_trace_axis_previous (k : Fin 4) :
    ((quadrantSeedMatrices (axisPreviousQuadrant k)).1 *
        (quadrantSeedMatrices (axisPreviousQuadrant k)).2).trace =
      3 * 3 - ((quadrantSeedMatrices k).1 * (quadrantSeedMatrices k).2).trace := by
  rw [(quadrantSeed_trace_triple (axisPreviousQuadrant k)).2.2,
    (quadrantSeed_trace_triple k).2.2]
  fin_cases k <;> norm_num [axisPreviousQuadrant]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Both selected values at an actual quadrant seed axis. The opposite ray
is the reversed seed ray of the preceding quadrant, not an assumed reflection. -/
theorem quadrant_axis_selected_values (B : Module.Basis (Fin 2) ℝ E)
    (htrace : QuadrantTraceLengthCompatible B) (k : Fin 4) :
    selectedSupportAt B (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
        (intVector B (quadrantSeedDirections k).2) =
        2 * Real.log (traceRealEmbedding 3 (traceCoefficient 3 3
          ((quadrantSeedMatrices k).1 * (quadrantSeedMatrices k).2).trace)) ∧
      selectedSupportAt B (quadrantSeedDirections k).1 (-(quadrantSeedDirections k).2)
        (intVector B (-(quadrantSeedDirections k).2)) =
        2 * Real.log (traceRealEmbedding 3 (traceCoefficient 3 3
          (3 * 3 - ((quadrantSeedMatrices k).1 * (quadrantSeedMatrices k).2).trace))) := by
  constructor
  · have hs : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
        (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
        (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
        (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 := .seed
    letI : Fact (3 ≤ (quadrantSeedMatrices k).1.trace) :=
      ⟨(quadrantSeed_positiveFrickePair k).trace_left⟩
    have hv := hs.selected_value B (quadrantSeed_positiveFrickePair k)
      (by rw [quadrantSeed_det_eq_one]; norm_num) (htrace k)
    rw [trace_coefficient_embedding_congr (quadrantSeed_trace_triple k).1] at hv
    simpa only [(quadrantSeed_trace_triple k).2.1] using hv
  · let j := axisPreviousQuadrant k
    have hs : SeededFarey (quadrantSeedDirections j).1 (quadrantSeedDirections j).2
        (quadrantSeedMatrices j).1 (quadrantSeedMatrices j).2
        (quadrantSeedDirections j).1 (quadrantSeedDirections j).2
        (quadrantSeedMatrices j).1 (quadrantSeedMatrices j).2 := .seed
    letI : Fact (3 ≤ (quadrantSeedMatrices j).2.trace) :=
      ⟨(quadrantSeed_positiveFrickePair j).trace_right⟩
    have hv := hs.reversed_selected_value B (quadrantSeed_positiveFrickePair j)
      (by rw [quadrantSeed_det_eq_one]; norm_num) (htrace j)
    rw [trace_coefficient_embedding_congr (quadrantSeed_trace_triple j).2.1] at hv
    simpa only [j, (quadrantSeedDirections_axis_previous k).1,
      (quadrantSeedDirections_axis_previous k).2,
      (quadrantSeed_trace_triple (axisPreviousQuadrant k)).1,
      (quadrantSeed_trace_triple (axisPreviousQuadrant k)).2.1,
      quadrantSeed_product_trace_axis_previous k] using hv

/-- The exact support jump at every actual quadrant seed axis. -/
theorem quadrant_axis_selected_jump (B : Module.Basis (Fin 2) ℝ E)
    (htrace : QuadrantTraceLengthCompatible B) (k : Fin 4) :
    selectedSupportAt B (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
        (intVector B (quadrantSeedDirections k).2) -
      selectedSupportAt B (quadrantSeedDirections k).1 (-(quadrantSeedDirections k).2)
        (intVector B (quadrantSeedDirections k).2) = analyticCornerJump 3 := by
  have hv := quadrant_axis_selected_values B htrace k
  have hneg : intVector B (-(quadrantSeedDirections k).2) =
      -intVector B (quadrantSeedDirections k).2 := by
    simp only [intVector, Prod.fst_neg, Prod.snd_neg, Int.cast_neg, neg_smul, neg_add]
  rw [hneg, map_neg] at hv
  have hf : (3 : ℤ) ^ 2 + 3 ^ 2 +
      ((quadrantSeedMatrices k).1 * (quadrantSeedMatrices k).2).trace ^ 2 =
      3 * 3 * ((quadrantSeedMatrices k).1 * (quadrantSeedMatrices k).2).trace := by
    simpa only [(quadrantSeed_trace_triple k).1,
      (quadrantSeed_trace_triple k).2.1] using (quadrantSeed_positiveFrickePair k).fricke
  have hj := traceCoefficient_conjugate_log_jump 3 3
    ((quadrantSeedMatrices k).1 * (quadrantSeedMatrices k).2).trace (by norm_num) hf
  norm_num only [Int.cast_ofNat] at hv hj
  linarith only [hv.1, hv.2, hj]

/-- Every seed axis has two different actual norming supports with the
explicit positive jump on its positively oriented adjacent seed direction. -/
theorem quadrant_axis_norming_supports (B : Module.Basis (Fin 2) ℝ E)
    (htrace : QuadrantTraceLengthCompatible B) (k : Fin 4) :
    ∃ f g : StrongDual ℝ E,
      f ∈ normingFunctionals (intVector B (quadrantSeedDirections k).1) ∧
      g ∈ normingFunctionals (intVector B (quadrantSeedDirections k).1) ∧
      f (intVector B (quadrantSeedDirections k).2) -
        g (intVector B (quadrantSeedDirections k).2) = analyticCornerJump 3 ∧
      f ≠ g := by
  let f := selectedSupportAt B (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
  let g := selectedSupportAt B (quadrantSeedDirections k).1 (-(quadrantSeedDirections k).2)
  have hdp : intDet (quadrantSeedDirections k).1 (quadrantSeedDirections k).2 ≠ 0 := by
    rw [quadrantSeed_det_eq_one]
    norm_num
  have hdm : intDet (quadrantSeedDirections k).1 (-(quadrantSeedDirections k).2) ≠ 0 := by
    have hd := quadrantSeed_det_eq_one k
    dsimp [intDet] at *
    intro hz
    nlinarith
  have hj : f (intVector B (quadrantSeedDirections k).2) -
      g (intVector B (quadrantSeedDirections k).2) = analyticCornerJump 3 :=
    quadrant_axis_selected_jump B htrace k
  refine ⟨f, g, (selectedSupportAt_spec B _ _ hdp).1,
    (selectedSupportAt_spec B _ _ hdm).1, hj, ?_⟩
  intro he
  rw [he, sub_self] at hj
  have hp := analyticCornerJump_pos 3 (by norm_num)
  linarith

/-- The constructed trace norm has the two distinct norming supports at
each of its four seed axes, without a remaining compatibility hypothesis. -/
theorem trace_quadrant_axis_norming_supports (k : Fin 4) :
    ∃ f g : StrongDual ℝ TracePlane,
      f ∈ normingFunctionals (intVector traceBasis (quadrantSeedDirections k).1) ∧
      g ∈ normingFunctionals (intVector traceBasis (quadrantSeedDirections k).1) ∧
      f (intVector traceBasis (quadrantSeedDirections k).2) -
        g (intVector traceBasis (quadrantSeedDirections k).2) = analyticCornerJump 3 ∧
      f ≠ g :=
  quadrant_axis_norming_supports traceBasis tracePlane_quadrantTraceLengthCompatible k

/-- Every quadrant axis has the common positive seed length. -/
theorem trace_quadrant_axis_norm (k : Fin 4) :
    ‖intVector traceBasis (quadrantSeedDirections k).1‖ = traceAxisLength := by
  fin_cases k <;> simp [quadrantSeedDirections, intVector]

/-- The two actual axis supports supply a lower bound for its actual
boundary turn atom. -/
theorem trace_axis_atom_lower (k : Fin 4) :
    ‖intVector traceBasis (quadrantSeedDirections k).1‖ * analyticCornerJump 3 /
        (‖traceBasis 0‖ + ‖traceBasis 1‖) ^ 2 ≤
      (traceBoundaryTurn
        {NormedSpace.normalize (intVector traceBasis (quadrantSeedDirections k).1)}).toReal := by
  obtain ⟨f, g, hf, hg, hj, _⟩ := trace_quadrant_axis_norming_supports k
  have hne : intVector traceBasis (quadrantSeedDirections k).1 ≠ 0 :=
    norm_pos_iff.mp (by rw [trace_quadrant_axis_norm]; exact traceAxisLength_pos)
  have hb := traceBoundaryTurn_atom_lower_of_direction_support_jump
    (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
    (by rw [quadrantSeed_det_eq_one]; norm_num) hne f g hf hg (analyticCornerJump 3) hj
  rwa [abs_of_pos (analyticCornerJump_pos 3 (by norm_num))] at hb

/-- The exponential lower bound for the actual atom at each seed axis. -/
theorem trace_axis_atom_exp_lower (k : Fin 4) :
    2 * ‖intVector traceBasis (quadrantSeedDirections k).1‖ *
        Real.exp (-‖intVector traceBasis (quadrantSeedDirections k).1‖) /
        (‖traceBasis 0‖ + ‖traceBasis 1‖) ^ 2 ≤
      (traceBoundaryTurn
        {NormedSpace.normalize (intVector traceBasis (quadrantSeedDirections k).1)}).toReal := by
  have hs : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2
      (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 := .seed
  have htrace := (tracePlane_quadrantTraceLengthCompatible k hs).1
  rw [(quadrantSeed_trace_triple k).1] at htrace
  norm_num only [Int.cast_ofNat] at htrace
  have hj := analyticCornerJump_ge_two_exp_neg_of_cosh 3
    ‖intVector traceBasis (quadrantSeedDirections k).1‖ (by norm_num)
    (norm_nonneg _) htrace
  apply le_trans _ (trace_axis_atom_lower k)
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hj
    (norm_nonneg (intVector traceBasis (quadrantSeedDirections k).1))]

end Markov
