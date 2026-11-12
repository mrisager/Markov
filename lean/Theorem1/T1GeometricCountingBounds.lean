import T1GeometricThreshold
import Markov.FiniteReciprocalCounting
import Markov.FiniteLatticeReciprocalSquare

/-! Genuine lattice norm equivalence, quadratic counting, and the linear
reciprocal-length estimate required by the Möbius hyperbola bound. -/

noncomputable section
open Classical Finset Set
namespace Markov

def t1_geometricComparisonConstant : ℝ := ‖traceEuclideanCoordinates‖ + 1

theorem t1_geometricComparisonConstant_pos : 0 < t1_geometricComparisonConstant := by
  unfold t1_geometricComparisonConstant
  positivity

theorem t1_geometricComparisonConstant_ge_one : 1 ≤ t1_geometricComparisonConstant := by
  unfold t1_geometricComparisonConstant
  linarith [norm_nonneg traceEuclideanCoordinates]

theorem t1_geometricLength_traceNorm (p : ℤ × ℤ) :
    t1_geometricLength p = ‖intVector traceBasis p‖ := by
  rw [t1_geometricLength, modularMcShaneRivinNorm_eq_traceEuclideanGauge,
    traceEuclideanGauge_intDirection]

theorem t1_euclidean_le_geometricLength (p : ℤ × ℤ) :
    intEuclidean p ≤ t1_geometricComparisonConstant * t1_geometricLength p := by
  rw [t1_geometricLength_traceNorm, ← euclideanIntDirection_norm,
    ← traceEuclideanCoordinates_intVector]
  exact (traceEuclideanCoordinates.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (by unfold t1_geometricComparisonConstant; linarith)
      (norm_nonneg _))

def t1_geometricMinimumLength : ℝ := 1 / t1_geometricComparisonConstant

theorem t1_geometricMinimumLength_pos : 0 < t1_geometricMinimumLength :=
  div_pos zero_lt_one t1_geometricComparisonConstant_pos

theorem t1_geometricLength_lower {p : ℤ × ℤ} (hp : p ≠ (0, 0)) :
    t1_geometricMinimumLength ≤ t1_geometricLength p := by
  apply (div_le_iff₀ t1_geometricComparisonConstant_pos).mpr
  have h := (intEuclidean_ge_one p hp).trans (t1_euclidean_le_geometricLength p)
  nlinarith

def t1_geometricCountingConstant : ℝ := 25 * t1_geometricComparisonConstant ^ 2

theorem t1_geometricCountingConstant_nonneg : 0 ≤ t1_geometricCountingConstant := by
  unfold t1_geometricCountingConstant
  positivity

/-- A proved count bound for every finite subset, in the original fixed
geometric norm. No quadratic-count field is supplied. -/
theorem t1_finite_geometric_count_le (S : Finset (ℤ × ℤ)) (T : ℝ)
    (hT : t1_geometricMinimumLength ≤ T) :
    ((S.filter (fun p => t1_geometricLength p ≤ T)).card : ℝ) ≤
      t1_geometricCountingConstant * T ^ 2 := by
  have hCT : 1 ≤ t1_geometricComparisonConstant * T := by
    have h := (div_le_iff₀ t1_geometricComparisonConstant_pos).mp hT
    nlinarith
  have hsub : S.filter (fun p => t1_geometricLength p ≤ T) ⊆
      S.filter (fun p => intEuclidean p ≤ t1_geometricComparisonConstant * T) := by
    intro p hp
    obtain ⟨hpS, hpT⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨hpS, ?_⟩
    exact (t1_euclidean_le_geometricLength p).trans
      (mul_le_mul_of_nonneg_left hpT t1_geometricComparisonConstant_pos.le)
  calc
    _ ≤ ((S.filter (fun p => intEuclidean p ≤ t1_geometricComparisonConstant * T)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ 25 * (t1_geometricComparisonConstant * T) ^ 2 :=
      finite_integer_direction_count_le_quadratic S _ hCT
    _ = _ := by unfold t1_geometricCountingConstant; ring

theorem t1_geometricNonzeroFinset_length_bounds (Y : ℝ) (hY : 0 < Y)
    {p : ℤ × ℤ} (hp : p ∈ t1_geometricNonzeroFinset Y hY) :
    t1_geometricMinimumLength ≤ t1_geometricLength p ∧ t1_geometricLength p ≤ Y := by
  obtain ⟨hne, hmem⟩ := (t1_mem_geometricNonzeroFinset Y hY p).mp hp
  exact ⟨t1_geometricLength_lower hne, (t1_mem_coordinate_norm_iff Y hY p).mp hmem⟩

theorem t1_geometricNonzeroFinset_empty_of_small (Y : ℝ) (hY : 0 < Y)
    (hsmall : Y < t1_geometricMinimumLength) :
    t1_geometricNonzeroFinset Y hY = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hb := t1_geometricNonzeroFinset_length_bounds Y hY hp
  linarith

theorem t1_geometricNonzeroFinset_card_le (Y : ℝ) (hY : 0 < Y) :
    ((t1_geometricNonzeroFinset Y hY).card : ℝ) ≤
      t1_geometricCountingConstant * Y ^ 2 := by
  by_cases hlarge : t1_geometricMinimumLength ≤ Y
  · have hall : (t1_geometricNonzeroFinset Y hY).filter
        (fun p => t1_geometricLength p ≤ Y) = t1_geometricNonzeroFinset Y hY :=
      Finset.filter_eq_self.mpr (fun p hp => (t1_geometricNonzeroFinset_length_bounds Y hY hp).2)
    simpa only [hall] using t1_finite_geometric_count_le (t1_geometricNonzeroFinset Y hY) Y hlarge
  · rw [t1_geometricNonzeroFinset_empty_of_small Y hY (lt_of_not_ge hlarge)]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg t1_geometricCountingConstant_nonneg (sq_nonneg Y)

def t1_geometricReciprocalConstant : ℝ :=
  t1_geometricCountingConstant * (t1_geometricComparisonConstant ^ 2 + 2)

theorem t1_geometricReciprocalConstant_nonneg : 0 ≤ t1_geometricReciprocalConstant := by
  unfold t1_geometricReciprocalConstant
  exact mul_nonneg t1_geometricCountingConstant_nonneg (by positivity)

/-- The reciprocal-length sum is linear in the actual geometric radius,
with no logarithmic loss. The short-radius case is proved by emptiness. -/
theorem t1_geometric_reciprocal_sum_le (Y : ℝ) (hY : 0 < Y) :
    (∑ p ∈ t1_geometricNonzeroFinset Y hY, 1 / t1_geometricLength p) ≤
      t1_geometricReciprocalConstant * Y := by
  simp only [one_div]
  by_cases hlarge : t1_geometricMinimumLength ≤ Y
  · have hmain := finite_sum_inv_le_of_count_quadratic
      (t1_geometricNonzeroFinset Y hY) t1_geometricLength
      t1_geometricCountingConstant 1 t1_geometricMinimumLength Y
      t1_geometricMinimumLength_pos hlarge t1_geometricCountingConstant_nonneg
      (by norm_num) (fun p hp => t1_geometricNonzeroFinset_length_bounds Y hY hp)
      (fun T hT _ => (t1_finite_geometric_count_le _ T hT).trans
        (by nlinarith [t1_geometricCountingConstant_nonneg]))
    have hCY : 1 ≤ t1_geometricComparisonConstant * Y := by
      have h := (div_le_iff₀ t1_geometricComparisonConstant_pos).mp hlarge
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hCY
      (mul_nonneg t1_geometricCountingConstant_nonneg t1_geometricComparisonConstant_pos.le)
    simp only [t1_geometricMinimumLength, one_div, div_inv_eq_mul, mul_one] at hmain
    unfold t1_geometricReciprocalConstant
    nlinarith
  · rw [t1_geometricNonzeroFinset_empty_of_small Y hY (lt_of_not_ge hlarge)]
    simp only [Finset.sum_empty]
    exact mul_nonneg t1_geometricReciprocalConstant_nonneg hY.le

end Markov
