import T1GeometricHyperbola
import T1MertensEnvelope
import T1GeometricCountingBounds

/-! The actual large-divisor bound R*Y*Delta(D), with Y=R/D. The envelope
is defined from the genuine arithmetic Möbius function; no decay rate is
assumed here, and no asymptotic cancellation is claimed. -/

noncomputable section
open Classical Finset Set
open scoped ArithmeticFunction.Moebius
namespace Markov

def t1_geometricMobiusTail (R : ℝ) (hR : 0 < R) (D : ℕ) : ℤ :=
  ∑ g ∈ Finset.Ioc D (t1_gcdCutoff (t1_geometricNonzeroFinset R hR)),
    μ g * ((modularMcShaneRivinLatticeCount (R / g) - 1 : ℕ) : ℤ)

theorem t1_geometric_tail_envelope_sum (R : ℝ) (hR : 0 < R) (D : ℕ) (hD : 0 < D) :
    |(t1_geometricMobiusTail R hR D : ℝ)| ≤
      t1_mertensEnvelope D *
        (R * (∑ p ∈ t1_geometricNonzeroFinset (R / D)
          (div_pos hR (by exact_mod_cast hD)), 1 / t1_geometricLength p) +
        (D : ℝ) * (t1_geometricNonzeroFinset (R / D)
          (div_pos hR (by exact_mod_cast hD))).card) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hdelta := t1_mertensEnvelope_nonneg D
  let S := t1_geometricNonzeroFinset (R / D) (div_pos hR hDR)
  have hpoint (p : ℤ × ℤ) (hp : p ∈ S) :
      |(t1_mertensNat (t1_geometricThreshold R p) : ℝ) - (t1_mertensNat D : ℝ)| ≤
        t1_mertensEnvelope D * (R / t1_geometricLength p + (D : ℝ)) := by
    obtain ⟨hne, hmem⟩ := (t1_mem_geometricNonzeroFinset _ _ p).mp hp
    have hL := t1_geometricLength_pos hne
    have hDT := (t1_geometricThreshold_iff R hR D hD p hne).mpr hmem
    have hfloor : (t1_geometricThreshold R p : ℝ) ≤ R / t1_geometricLength p :=
      Nat.floor_le (div_nonneg hR.le hL.le)
    calc
      _ ≤ |(t1_mertensNat (t1_geometricThreshold R p) : ℝ)| + |(t1_mertensNat D : ℝ)| :=
        abs_sub _ _
      _ ≤ t1_mertensEnvelope D * t1_geometricThreshold R p + t1_mertensEnvelope D * D :=
        add_le_add (t1_mertensEnvelope_dominates D _ hDT)
          (t1_mertensEnvelope_dominates D D le_rfl)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hfloor hdelta]
  rw [t1_geometricMobiusTail, t1_geometric_mobius_tail_hyperbola R hR D hD]
  simp only [Int.cast_sum, Int.cast_sub]
  change |∑ p ∈ S, ((t1_mertensNat (t1_geometricThreshold R p) : ℝ) - (t1_mertensNat D : ℝ))| ≤ _
  calc
    _ ≤ ∑ p ∈ S, |(t1_mertensNat (t1_geometricThreshold R p) : ℝ) - (t1_mertensNat D : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, t1_mertensEnvelope D * (R / t1_geometricLength p + (D : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = _ := by
      change (∑ p ∈ S, t1_mertensEnvelope D * (R / t1_geometricLength p + (D : ℝ))) =
        t1_mertensEnvelope D * (R * (∑ p ∈ S, 1 / t1_geometricLength p) + (D : ℝ) * S.card)
      simp only [mul_add, Finset.sum_add_distrib, div_eq_mul_inv, one_mul,
        ← mul_assoc, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring

def t1_geometricTailConstant : ℝ :=
  t1_geometricReciprocalConstant + t1_geometricCountingConstant

theorem t1_geometricTailConstant_pos : 0 < t1_geometricTailConstant := by
  have hcompare := t1_geometricComparisonConstant_pos
  have hc : 0 < t1_geometricCountingConstant := by
    unfold t1_geometricCountingConstant
    positivity
  exact add_pos_of_nonneg_of_pos t1_geometricReciprocalConstant_nonneg hc

/-- The genuine large-divisor estimate in the paper. Both lattice bounds
and the uniform Mertens envelope bound have been discharged by theorems. -/
theorem t1_geometric_mobius_tail_bound (R : ℝ) (hR : 0 < R) (D : ℕ) (hD : 0 < D) :
    |(t1_geometricMobiusTail R hR D : ℝ)| ≤
      t1_geometricTailConstant * R * (R / D) * t1_mertensEnvelope D := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hY : 0 < R / D := div_pos hR hDR
  have hdelta := t1_mertensEnvelope_nonneg D
  calc
    _ ≤ t1_mertensEnvelope D *
        (R * (∑ p ∈ t1_geometricNonzeroFinset (R / D) hY, 1 / t1_geometricLength p) +
        (D : ℝ) * (t1_geometricNonzeroFinset (R / D) hY).card) :=
      t1_geometric_tail_envelope_sum R hR D hD
    _ ≤ t1_mertensEnvelope D *
        (R * (t1_geometricReciprocalConstant * (R / D)) +
        (D : ℝ) * (t1_geometricCountingConstant * (R / D) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (t1_geometric_reciprocal_sum_le _ hY) hR.le)
          (mul_le_mul_of_nonneg_left (t1_geometricNonzeroFinset_card_le _ hY) hDR.le)) hdelta
    _ = _ := by
      unfold t1_geometricTailConstant
      field_simp [hDR.ne']

end Markov
