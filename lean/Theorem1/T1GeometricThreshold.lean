import T1GeometricMobius

noncomputable section
open Classical Finset Set
namespace Markov

/-- The length is the genuine intrinsic geometric norm in original A/B
integer coordinates. No trace value occurs in this definition. -/
def t1_geometricLength (p : ℤ × ℤ) : ℝ :=
  modularMcShaneRivinNorm (euclideanIntDirection p)

theorem t1_geometricLength_pos {p : ℤ × ℤ} (hp : p ≠ (0, 0)) :
    0 < t1_geometricLength p := by
  have hnonneg := modularMcShaneRivinNorm_nonneg (euclideanIntDirection p)
  apply lt_of_le_of_ne hnonneg
  intro hz
  have hvec := (modularMcShaneRivinNorm_eq_zero_iff _).mp hz.symm
  apply hp
  apply Prod.ext
  · have h0 := congrArg (fun x => x 0) hvec
    simpa [euclideanIntDirection] using h0
  · have h1 := congrArg (fun x => x 1) hvec
    simpa [euclideanIntDirection] using h1

def t1_geometricThreshold (R : ℝ) (p : ℤ × ℤ) : ℕ :=
  ⌊R / t1_geometricLength p⌋₊

/-- Actual membership at radius R/g is the integer threshold inequality. -/
theorem t1_geometricThreshold_iff (R : ℝ) (hR : 0 < R) (g : ℕ) (hg : 0 < g)
    (p : ℤ × ℤ) (hp : p ≠ (0, 0)) :
    g ≤ t1_geometricThreshold R p ↔ p ∈ modularMcShaneRivinCoordinateSet (R / g) := by
  have hpL := t1_geometricLength_pos hp
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  rw [t1_mem_coordinate_norm_iff _ (div_pos hR hgR)]
  change g ≤ ⌊R / t1_geometricLength p⌋₊ ↔ t1_geometricLength p ≤ R / g
  rw [Nat.le_floor_iff (div_nonneg hR.le hpL.le), le_div_iff₀ hpL,
    le_div_iff₀ hgR]
  constructor <;> intro h <;> nlinarith

/-- The computed gcd cutoff bounds the actual threshold of every nonzero
integer point. This proves finiteness of the divisor sum geometrically. -/
theorem t1_geometricThreshold_le_cutoff (R : ℝ) (hR : 0 < R)
    (p : ℤ × ℤ) (hp : p ≠ (0, 0)) :
    t1_geometricThreshold R p ≤ t1_gcdCutoff (t1_geometricNonzeroFinset R hR) := by
  by_cases hpos : 0 < t1_geometricThreshold R p
  · have hmem := (t1_geometricThreshold_iff R hR _ hpos p hp).mp le_rfl
    have hsmall : p ∈ t1_geometricNonzeroFinset
        (R / t1_geometricThreshold R p) (div_pos hR (by exact_mod_cast hpos)) :=
      (t1_mem_geometricNonzeroFinset _ _ _).mpr ⟨hp, hmem⟩
    have hscaled : (t1_geometricThreshold R p) • p ∈
        ((t1_geometricNonzeroFinset R hR).filter
          (fun q => t1_geometricThreshold R p ∣ Int.gcd q.1 q.2)) := by
      rw [← t1_geometric_divisor_fiber_image R hR _ hpos]
      exact Finset.mem_image.mpr ⟨p, hsmall, rfl⟩
    obtain ⟨hpoint, hdvd⟩ := Finset.mem_filter.mp hscaled
    have hne := ((t1_mem_geometricNonzeroFinset R hR _).mp hpoint).1
    exact (Nat.le_of_dvd (integerPair_gcd_pos hne) hdvd).trans
      (t1_gcd_le_cutoff _ hpoint)
  · omega

end Markov
