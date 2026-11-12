import Markov.FrontierIndex
import Markov.SeedEvaluation
import Markov.SeedProfiles
import Markov.AxisCorner

/-! Exact finite-frontier edges adjacent to the seed axes. Both labels and
replacement-seed matrix values are calculated, so the axis-ray inequalities
can be applied to the actual signed profiles. -/

namespace Markov

/-- Uniform two-child refinement gives the left child at every even index. -/
theorem farey_refine_getD_even (es : List FareyEdge) (i : ℕ) (hi : i < es.length) :
    (es.flatMap FareyEdge.refine).getD (2 * i) FareyEdge.seed =
      (es.getD i FareyEdge.seed).left := by
  induction es generalizing i with
  | nil => simp at hi
  | cons e es ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi' : i < es.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
      simpa [FareyEdge.refine, Nat.mul_succ] using ih i hi'

/-- The right child occurs at the following odd index. -/
theorem farey_refine_getD_odd (es : List FareyEdge) (i : ℕ) (hi : i < es.length) :
    (es.flatMap FareyEdge.refine).getD (2 * i + 1) FareyEdge.seed =
      (es.getD i FareyEdge.seed).right := by
  induction es generalizing i with
  | nil => simp at hi
  | cons e es ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi' : i < es.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
      simpa [FareyEdge.refine, Nat.mul_succ] using ih i hi'

/-- Every new first edge is the left child of the old first edge. -/
theorem indexedFareyEdge_first_succ (n : ℕ) :
    indexedFareyEdge (n + 1) 0 = (indexedFareyEdge n 0).left := by
  have h := farey_refine_getD_even (fareyFrontier n) 0
    (by rw [fareyFrontier_length]; positivity)
  simpa only [indexedFareyEdge, fareyFrontier, Nat.mul_zero] using h

/-- Every new terminal edge is the right child of the old terminal edge. -/
theorem indexedFareyEdge_last_succ (n : ℕ) :
    indexedFareyEdge (n + 1) (2 ^ (n + 1) - 1) =
      (indexedFareyEdge n (2 ^ n - 1)).right := by
  have hp : 0 < 2 ^ n := by positivity
  have hi : 2 ^ n - 1 < (fareyFrontier n).length := by rw [fareyFrontier_length]; omega
  have h := farey_refine_getD_odd (fareyFrontier n) (2 ^ n - 1) hi
  have he : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by rw [pow_succ]; omega
  simpa only [indexedFareyEdge, fareyFrontier, he] using h

/-- The actual first edge ends at the left integral ray. -/
theorem indexedFareyEdge_first_neighbor (n : ℕ) :
    (indexedFareyEdge n 0).v = n • (1, 0) + (0, 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [indexedFareyEdge_first_succ]
    change (indexedFareyEdge n 0).u + (indexedFareyEdge n 0).v = _
    rw [indexedFareyEdge_first, ih, add_nsmul, one_nsmul]
    abel

/-- The actual last edge starts at the right integral ray. -/
theorem indexedFareyEdge_last_neighbor (n : ℕ) :
    (indexedFareyEdge n (2 ^ n - 1)).u = (1, 0) + n • (0, 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [indexedFareyEdge_last_succ]
    change (indexedFareyEdge n (2 ^ n - 1)).u + (indexedFareyEdge n (2 ^ n - 1)).v = _
    rw [indexedFareyEdge_last, ih, add_nsmul, one_nsmul]
    abel

/-- The first replacement-seed edge has the exact matrix ray M^n N. -/
theorem seedEvaluation_first_axis (M0 N0 : IntMatrixTwo) (n : ℕ) :
    seedEvaluation M0 N0 (indexedFareyEdge n 0) = (M0, M0 ^ n * N0) := by
  induction n with
  | zero => simpa only [indexedFareyEdge, fareyFrontier, List.getD_cons_zero, pow_zero, one_mul]
      using seedEvaluation_seed M0 N0
  | succ n ih =>
    rw [indexedFareyEdge_first_succ, seedEvaluation_left, ih]
    simp only [pow_succ', Matrix.mul_assoc]

/-- The terminal replacement-seed edge has the complementary ray MN^n. -/
theorem seedEvaluation_last_axis (M0 N0 : IntMatrixTwo) (n : ℕ) :
    seedEvaluation M0 N0 (indexedFareyEdge n (2 ^ n - 1)) = (M0 * N0 ^ n, N0) := by
  induction n with
  | zero => simpa only [indexedFareyEdge, fareyFrontier, pow_zero, Nat.sub_self,
      List.getD_cons_zero, mul_one] using seedEvaluation_seed M0 N0
  | succ n ih =>
    rw [indexedFareyEdge_last_succ, seedEvaluation_right, ih]
    simp only [pow_succ, Matrix.mul_assoc]

/-- The left endpoint length uses the actual evaluated matrix trace. -/
theorem seedEdgeLengthU_eq_seedEvaluation (M0 N0 : IntMatrixTwo) (e : FareyEdge) :
    seedEdgeLengthU M0 N0 e =
      2 * Real.arcosh ((((seedEvaluation M0 N0 e).1).trace : ℝ) / 2) := by
  rw [seedEdgeLengthU, primitiveSeedLength, primitiveSeedTrace,
    (seedEvaluation_spec M0 N0 e).primitiveSeedMatrix_left]

/-- The right endpoint length uses the actual evaluated matrix trace. -/
theorem seedEdgeLengthV_eq_seedEvaluation (M0 N0 : IntMatrixTwo) (e : FareyEdge) :
    seedEdgeLengthV M0 N0 e =
      2 * Real.arcosh ((((seedEvaluation M0 N0 e).2).trace : ℝ) / 2) := by
  rw [seedEdgeLengthV, primitiveSeedLength, primitiveSeedTrace,
    (seedEvaluation_spec M0 N0 e).primitiveSeedMatrix_right]

/-- The first affine offset is the length of the first seed axis. -/
theorem seedEdgeOffset_first_axis (M0 N0 : IntMatrixTwo) (n : ℕ) :
    seedEdgeOffset M0 N0 (indexedFareyEdge n 0) =
      2 * Real.arcosh ((M0.trace : ℝ) / 2) := by
  simp [seedEdgeOffset, profileOffset, indexedFareyEdge_first,
    indexedFareyEdge_first_neighbor, seedEdgeLengthU_eq_seedEvaluation,
    seedEvaluation_first_axis]

/-- Evaluating the first affine line at one leaves the exact axis-ray
length minus its integral axis contribution. -/
theorem seedEdgeOffset_add_slope_first_axis (M0 N0 : IntMatrixTwo) (n : ℕ) :
    seedEdgeOffset M0 N0 (indexedFareyEdge n 0) +
        seedEdgeSlope M0 N0 (indexedFareyEdge n 0) =
      2 * Real.arcosh (((M0 ^ n * N0).trace : ℝ) / 2) -
        (n : ℝ) * (2 * Real.arcosh ((M0.trace : ℝ) / 2)) := by
  simp [seedEdgeOffset, seedEdgeSlope, profileOffset, profileSlope, profileMass,
    indexedFareyEdge_first, indexedFareyEdge_first_neighbor,
    seedEdgeLengthU_eq_seedEvaluation, seedEdgeLengthV_eq_seedEvaluation,
    seedEvaluation_first_axis]
  ring

/-- The final affine offset uses the complementary actual matrix ray. -/
theorem seedEdgeOffset_last_axis (M0 N0 : IntMatrixTwo) (n : ℕ) :
    seedEdgeOffset M0 N0 (indexedFareyEdge n (2 ^ n - 1)) =
      2 * Real.arcosh (((M0 * N0 ^ n).trace : ℝ) / 2) -
        (n : ℝ) * (2 * Real.arcosh ((N0.trace : ℝ) / 2)) := by
  simp [seedEdgeOffset, profileOffset, indexedFareyEdge_last,
    indexedFareyEdge_last_neighbor, seedEdgeLengthU_eq_seedEvaluation,
    seedEdgeLengthV_eq_seedEvaluation, seedEvaluation_last_axis]
  ring

/-- Evaluating the final affine line at one gives the second seed axis. -/
theorem seedEdgeOffset_add_slope_last_axis (M0 N0 : IntMatrixTwo) (n : ℕ) :
    seedEdgeOffset M0 N0 (indexedFareyEdge n (2 ^ n - 1)) +
        seedEdgeSlope M0 N0 (indexedFareyEdge n (2 ^ n - 1)) =
      2 * Real.arcosh ((N0.trace : ℝ) / 2) := by
  simp [seedEdgeOffset, seedEdgeSlope, profileOffset, profileSlope, profileMass,
    indexedFareyEdge_last, indexedFareyEdge_last_neighbor,
    seedEdgeLengthU_eq_seedEvaluation, seedEdgeLengthV_eq_seedEvaluation,
    seedEvaluation_last_axis]
  ring

/-- Transferring adjugation across a two-dimensional trace identifies the
opposite matrix ray used at a neighboring quadrant's axis. -/
theorem matrix_two_trace_adjugate_power_mul {R : Type*} [CommRing R]
    (A B : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    (A.adjugate ^ n * B).trace = (A ^ n * B.adjugate).trace := by
  have h := matrix_two_trace_adjugate (A ^ n * B.adjugate)
  simp only [Matrix.adjugate_mul_distrib, Matrix.adjugate_pow, Matrix.adjugate_adjugate',
    Fintype.card_fin, Nat.sub_self, pow_zero, one_smul] at h
  rw [Matrix.trace_mul_comm]
  exact h

end Markov
