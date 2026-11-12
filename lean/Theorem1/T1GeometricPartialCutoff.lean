import T1SmallDivisorHead
import T1GeometricTailBound

/-! The genuine geometric cutoff estimate, before replacing the finite
Möbius square sum by its infinite value. No decay of the actual Mertens
envelope is assumed in this module. -/

noncomputable section
open Classical Finset Set
open scoped ArithmeticFunction.Moebius
namespace Markov

theorem t1_geometric_primitive_head_tail (R : ℝ) (hR : 0 < R) (D : ℕ)
    (hDB : D ≤ t1_gcdCutoff (t1_geometricNonzeroFinset R hR)) :
    (t1_geometricPrimitiveCount R : ℝ) =
      t1_geometricMobiusHead R D + (t1_geometricMobiusTail R hR D : ℝ) := by
  let B := t1_gcdCutoff (t1_geometricNonzeroFinset R hR)
  let c : ℕ → ℝ := fun g => (μ g : ℝ) *
    ((modularMcShaneRivinLatticeCount (R / g) - 1 : ℕ) : ℝ)
  have hfull : (t1_geometricPrimitiveCount R : ℝ) = ∑ g ∈ Finset.Icc 1 B, c g := by
    have hcast := congrArg (fun z : ℤ => (z : ℝ))
      (t1_geometricPrimitiveCount_moebius_full R hR)
    simpa only [Int.cast_natCast, Int.cast_sum, Int.cast_mul, B, c] using hcast
  have hsub : Finset.Icc 1 D ⊆ Finset.Icc 1 B := by
    intro g hg
    obtain ⟨h1, hD⟩ := Finset.mem_Icc.mp hg
    exact Finset.mem_Icc.mpr ⟨h1, hD.trans hDB⟩
  have hdiff : Finset.Icc 1 B \ Finset.Icc 1 D = Finset.Ioc D B := by
    ext g
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsum := Finset.sum_sdiff hsub (f := c)
  rw [hdiff] at hsum
  have htail : (t1_geometricMobiusTail R hR D : ℝ) = ∑ g ∈ Finset.Ioc D B, c g := by
    simp only [t1_geometricMobiusTail, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    rfl
  rw [hfull, htail]
  change (∑ g ∈ Finset.Icc 1 B, c g) =
    (∑ g ∈ Finset.Icc 1 D, c g) + (∑ g ∈ Finset.Ioc D B, c g)
  linarith

/-- A literal nonzero lattice vector proves admissibility of the computed
gcd cutoff. Its norm is a genuine geometric value, not a free parameter. -/
theorem t1_geometric_cutoff_admissible (R : ℝ) (hR : 0 < R) (D : ℕ)
    (hcut : t1_geometricLength (1, 0) ≤ R / (D + 1)) :
    D ≤ t1_gcdCutoff (t1_geometricNonzeroFinset R hR) := by
  have hg : 0 < D + 1 := Nat.succ_pos _
  have hgR : (0 : ℝ) < D + 1 := by positivity
  have hmem : (1, 0) ∈ modularMcShaneRivinCoordinateSet (R / (D + 1)) :=
    (t1_mem_coordinate_norm_iff _ (div_pos hR hgR) (1, 0)).mpr hcut
  have hDT := (t1_geometricThreshold_iff R hR (D + 1) hg (1, 0) (by decide)).mpr
    (by simpa only [Nat.cast_add, Nat.cast_one] using hmem)
  have hTB := t1_geometricThreshold_le_cutoff R hR (1, 0) (by decide)
  omega

/-- Uniform cutoff estimate in the genuine ball and original lattice.
The remaining finite-square-sum tail and arithmetic decay estimates are
not silently assumed or included in this conclusion. -/
theorem t1_geometric_partial_cutoff_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 1 < T ∧
      ∀ R : ℝ, 0 < R → ∀ D : ℕ, 0 < D → T ≤ R / (D + 1) →
        |(t1_geometricPrimitiveCount R : ℝ) -
          modularMcShaneRivinArea * R ^ 2 * t1_moebiusSquarePartial D| ≤
          C * (R * (t1_headLog R (D + 1)) ^ (-(1 : ℝ) / 2) +
            R * (R / D) * t1_mertensEnvelope D) := by
  obtain ⟨C, hC, T, hT, hhead⟩ := t1_geometric_small_divisor_bound
  refine ⟨C + t1_geometricTailConstant, add_pos hC t1_geometricTailConstant_pos,
    max T (t1_geometricLength (1, 0)), hT.trans_le (le_max_left _ _), ?_⟩
  intro R hR D hD hcut
  have hcutT := (le_max_left T (t1_geometricLength (1, 0))).trans hcut
  have hcutP := (le_max_right T (t1_geometricLength (1, 0))).trans hcut
  have hDB := t1_geometric_cutoff_admissible R hR D hcutP
  have hsplit := t1_geometric_primitive_head_tail R hR D hDB
  have hh := hhead R hR D hcutT
  have ht := t1_geometric_mobius_tail_bound R hR D hD
  let a := R * (t1_headLog R (D + 1)) ^ (-(1 : ℝ) / 2)
  let b := R * (R / D) * t1_mertensEnvelope D
  have hlog : 0 < t1_headLog R (D + 1) := by
    rw [t1_headLog, ← Real.log_div hR.ne' (by positivity : (D : ℝ) + 1 ≠ 0)]
    exact Real.log_pos (hT.trans_le hcutT)
  have ha : 0 ≤ a := mul_nonneg hR.le (Real.rpow_nonneg hlog.le _)
  have hb : 0 ≤ b := by
    exact mul_nonneg (mul_nonneg hR.le (div_nonneg hR.le (Nat.cast_nonneg _)))
      (t1_mertensEnvelope_nonneg D)
  have herr : (t1_geometricPrimitiveCount R : ℝ) -
      modularMcShaneRivinArea * R ^ 2 * t1_moebiusSquarePartial D =
        (t1_geometricMobiusHead R D -
          modularMcShaneRivinArea * R ^ 2 * t1_moebiusSquarePartial D) +
          (t1_geometricMobiusTail R hR D : ℝ) := by rw [hsplit]; ring
  rw [herr]
  calc
    _ ≤ |t1_geometricMobiusHead R D -
        modularMcShaneRivinArea * R ^ 2 * t1_moebiusSquarePartial D| +
        |(t1_geometricMobiusTail R hR D : ℝ)| := abs_add_le _ _
    _ ≤ C * a + t1_geometricTailConstant * b := by
      have hh' : |t1_geometricMobiusHead R D -
          modularMcShaneRivinArea * R ^ 2 * t1_moebiusSquarePartial D| ≤ C * a := by
        dsimp [a]; nlinarith [hh]
      have ht' : |(t1_geometricMobiusTail R hR D : ℝ)| ≤ t1_geometricTailConstant * b := by
        dsimp [b]; nlinarith [ht]
      exact add_le_add hh' ht'
    _ ≤ (C + t1_geometricTailConstant) * (a + b) := by
      have h1 := mul_nonneg hC.le hb
      have h2 := mul_nonneg t1_geometricTailConstant_pos.le ha
      nlinarith

end Markov
