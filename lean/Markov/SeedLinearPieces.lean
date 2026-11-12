import Markov.SeedEnvelope
import Markov.QuadrantSeminormGlue

/-! Linear lifts of the checked seed profiles to an arbitrary based real plane.
The order and minimum bounds are derived from the actual seed crossings. -/

noncomputable section
namespace Markov

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The homogeneous linear lift of one seed profile. -/
def seedLinearPiece (B : Module.Basis (Fin 2) ℝ E) (M0 N0 : IntMatrixTwo)
    (n i : ℕ) : E →ₗ[ℝ] ℝ :=
  seedFrontierOffsets M0 N0 n i • B.coord 0 +
    (seedFrontierOffsets M0 N0 n i + seedFrontierSlopes M0 N0 n i) • B.coord 1

@[simp] theorem seedLinearPiece_apply_basis_zero (B : Module.Basis (Fin 2) ℝ E)
    (M0 N0 : IntMatrixTwo) (n i : ℕ) :
    seedLinearPiece B M0 N0 n i (B 0) = seedFrontierOffsets M0 N0 n i := by
  simp [seedLinearPiece, Module.Basis.coord_apply, Module.Basis.repr_self]

@[simp] theorem seedLinearPiece_apply_basis_one (B : Module.Basis (Fin 2) ℝ E)
    (M0 N0 : IntMatrixTwo) (n i : ℕ) :
    seedLinearPiece B M0 N0 n i (B 1) =
      seedFrontierOffsets M0 N0 n i + seedFrontierSlopes M0 N0 n i := by
  simp [seedLinearPiece, Module.Basis.coord_apply, Module.Basis.repr_self]

theorem seedLinearPiece_apply (B : Module.Basis (Fin 2) ℝ E)
    (M0 N0 : IntMatrixTwo) (n i : ℕ) (s t : ℝ) :
    seedLinearPiece B M0 N0 n i (s • B 0 + t • B 1) =
      s * seedFrontierOffsets M0 N0 n i +
        t * (seedFrontierOffsets M0 N0 n i + seedFrontierSlopes M0 N0 n i) := by
  simp only [map_add, map_smul, smul_eq_mul, seedLinearPiece_apply_basis_zero,
    seedLinearPiece_apply_basis_one]

/-- Normalization to the affine section gives exactly the checked seed profile. -/
theorem seedLinearPiece_profile (B : Module.Basis (Fin 2) ℝ E)
    (M0 N0 : IntMatrixTwo) (n i : ℕ) (s t : ℝ) (hsum : s + t ≠ 0) :
    seedLinearPiece B M0 N0 n i (s • B 0 + t • B 1) =
      (s + t) * seedEdgeProfile M0 N0 (indexedFareyEdge n i) (t / (s + t)) := by
  rw [seedLinearPiece_apply]
  simp only [seedEdgeProfile, seedFrontierOffsets, seedFrontierSlopes]
  field_simp
  ring

/-- The exterior-piece lower bound holds on the full nonnegative cone. -/
theorem seedLinearPiece_min_on_cone (B : Module.Basis (Fin 2) ℝ E)
    (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0) (n : ℕ)
    (x : E) (hx : x ∈ twoRayCone (B 0) (B 1)) (i : ℕ) (hi : i ≤ 2 ^ n - 1) :
    min (seedLinearPiece B M0 N0 n 0 x) (seedLinearPiece B M0 N0 n (2 ^ n - 1) x) ≤
      seedLinearPiece B M0 N0 n i x := by
  apply linearFamily_min_on_cone (seedLinearPiece B M0 N0 n) (2 ^ n - 1)
    (B 0) (B 1) (frontierBreakpoints n) ?_ ?_ ?_ x hx i hi
  · intro j hj
    simpa only [seedLinearPiece_apply_basis_zero, seedLinearPiece_apply_basis_one,
      add_sub_cancel_left] using seedFrontierSlopes_adjacent M0 N0 h0 n j hj
  · intro j hj
    simpa only [seedLinearPiece_apply_basis_zero, seedLinearPiece_apply_basis_one,
      add_sub_cancel_left] using seedFrontierProfiles_match M0 N0 n j hj
  · intro j k hjk hk
    exact frontierBreakpoints_mono n j k hjk (by omega)

/-- Consecutive pieces decrease on the first axis. -/
theorem seedLinearPiece_basis_zero_adjacent (B : Module.Basis (Fin 2) ℝ E)
    (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (n j : ℕ) (hj : j < 2 ^ n - 1) :
    seedLinearPiece B M0 N0 n (j + 1) (B 0) ≤ seedLinearPiece B M0 N0 n j (B 0) := by
  have hb : 0 ≤ frontierBreakpoints n j :=
    profileParameter_nonneg _ (indexedFareyEdge n j).holonomy.right_nonnegativePrimitive
  have h := affinePiece_le_left _ _ _ _ (frontierBreakpoints n j) 0
    (seedFrontierSlopes_adjacent M0 N0 h0 n j hj)
    (seedFrontierProfiles_match M0 N0 n j hj) hb
  simpa only [affinePiece, mul_zero, zero_add, seedLinearPiece_apply_basis_zero] using h

/-- Consecutive pieces increase on the second axis. -/
theorem seedLinearPiece_basis_one_adjacent (B : Module.Basis (Fin 2) ℝ E)
    (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (n j : ℕ) (hj : j < 2 ^ n - 1) :
    seedLinearPiece B M0 N0 n j (B 1) ≤ seedLinearPiece B M0 N0 n (j + 1) (B 1) := by
  have hb : frontierBreakpoints n j ≤ 1 :=
    profileParameter_le_one _ (indexedFareyEdge n j).holonomy.right_nonnegativePrimitive
  have h := affinePiece_le_right _ _ _ _ (frontierBreakpoints n j) 1
    (seedFrontierSlopes_adjacent M0 N0 h0 n j hj)
    (seedFrontierProfiles_match M0 N0 n j hj) hb
  simpa only [affinePiece, mul_one, seedLinearPiece_apply_basis_one, add_comm] using h

theorem seedLinearPiece_basis_zero_antitone (B : Module.Basis (Fin 2) ℝ E)
    (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (n i j : ℕ) (hij : i ≤ j) (hj : j < 2 ^ n) :
    seedLinearPiece B M0 N0 n j (B 0) ≤ seedLinearPiece B M0 N0 n i (B 0) := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (seedLinearPiece_basis_zero_adjacent B M0 N0 h0 n j (by omega)).trans (ih (by omega))

theorem seedLinearPiece_basis_one_monotone (B : Module.Basis (Fin 2) ℝ E)
    (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (n i j : ℕ) (hij : i ≤ j) (hj : j < 2 ^ n) :
    seedLinearPiece B M0 N0 n i (B 1) ≤ seedLinearPiece B M0 N0 n j (B 1) := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (ih (by omega)).trans (seedLinearPiece_basis_one_adjacent B M0 N0 h0 n j (by omega))

theorem seedLinearPiece_basis_zero_bounds (B : Module.Basis (Fin 2) ℝ E)
    (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (n i : ℕ) (hi : i ≤ 2 ^ n - 1) :
    seedLinearPiece B M0 N0 n (2 ^ n - 1) (B 0) ≤ seedLinearPiece B M0 N0 n i (B 0) ∧
      seedLinearPiece B M0 N0 n i (B 0) ≤ seedLinearPiece B M0 N0 n 0 (B 0) := by
  have hn := Nat.two_pow_pos n
  exact ⟨seedLinearPiece_basis_zero_antitone B M0 N0 h0 n i _ hi (by omega),
    seedLinearPiece_basis_zero_antitone B M0 N0 h0 n 0 i (Nat.zero_le _) (by omega)⟩

theorem seedLinearPiece_basis_one_bounds (B : Module.Basis (Fin 2) ℝ E)
    (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (n i : ℕ) (hi : i ≤ 2 ^ n - 1) :
    seedLinearPiece B M0 N0 n 0 (B 1) ≤ seedLinearPiece B M0 N0 n i (B 1) ∧
      seedLinearPiece B M0 N0 n i (B 1) ≤ seedLinearPiece B M0 N0 n (2 ^ n - 1) (B 1) := by
  have hn := Nat.two_pow_pos n
  exact ⟨seedLinearPiece_basis_one_monotone B M0 N0 h0 n 0 i (Nat.zero_le _) (by omega),
    seedLinearPiece_basis_one_monotone B M0 N0 h0 n i _ hi (by omega)⟩

end Markov
