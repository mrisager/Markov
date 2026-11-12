import T1GeometricPrimitiveCount
import T1IntegerDivisibility

/-! Exact Möbius inversion at geometric radii R/g. All divisor-fiber
identifications use actual signed integer multiplication and the proved
homogeneity of the genuine intrinsic norm. -/

noncomputable section
open Classical Finset Set
open scoped ArithmeticFunction.Moebius
open scoped Pointwise
namespace Markov

theorem t1_mem_coordinate_norm_iff (R : ℝ) (hR : 0 < R) (p : ℤ × ℤ) :
    p ∈ modularMcShaneRivinCoordinateSet R ↔
      modularMcShaneRivinNorm (euclideanIntDirection p) ≤ R := by
  change euclideanIntDirection p ∈ R • modularMcShaneRivinBall ↔ _
  rw [modularMcShaneRivinBall_eq_traceEuclideanBall]
  simpa only [modularMcShaneRivinNorm_eq_traceEuclideanGauge] using
    mem_smul_traceEuclideanBall_iff R hR (euclideanIntDirection p)

theorem t1_euclidean_direction_nsmul (g : ℕ) (p : ℤ × ℤ) :
    euclideanIntDirection (g • p) = (g : ℝ) • euclideanIntDirection p := by
  ext i
  fin_cases i <;> simp [euclideanIntDirection, nsmul_eq_mul]

theorem t1_intrinsic_norm_nsmul (g : ℕ) (p : ℤ × ℤ) :
    modularMcShaneRivinNorm (euclideanIntDirection (g • p)) =
      (g : ℝ) * modularMcShaneRivinNorm (euclideanIntDirection p) := by
  rw [t1_euclidean_direction_nsmul, modularMcShaneRivinNorm_smul,
    abs_of_nonneg (Nat.cast_nonneg g)]

theorem t1_geometric_zero_mem (R : ℝ) (hR : 0 < R) :
    (0, 0) ∈ modularMcShaneRivinCoordinateSet R := by
  apply (t1_mem_coordinate_norm_iff R hR (0, 0)).mpr
  have hz : euclideanIntDirection (0, 0) = 0 := by
    ext i
    fin_cases i <;> simp [euclideanIntDirection]
  rw [hz, modularMcShaneRivinNorm_zero]
  exact hR.le

theorem t1_geometricNonzero_card (R : ℝ) (hR : 0 < R) :
    (t1_geometricNonzeroFinset R hR).card = modularMcShaneRivinLatticeCount R - 1 := by
  let C := (modularMcShaneRivinCoordinateSet_finite R hR).toFinset
  have hz : (0, 0) ∈ C := by
    simpa only [C, Set.Finite.mem_toFinset] using t1_geometric_zero_mem R hR
  have heq : t1_geometricNonzeroFinset R hR = C.erase (0, 0) := by
    ext p
    simp only [t1_mem_geometricNonzeroFinset, C, Finset.mem_erase,
      Set.Finite.mem_toFinset]
  rw [heq, Finset.card_erase_of_mem hz,
    modularMcShaneRivinLatticeCount_eq_coordinate_ncard,
    Set.ncard_eq_toFinset_card _ (modularMcShaneRivinCoordinateSet_finite R hR)]

theorem t1_geometricLatticeCount_pos (R : ℝ) (hR : 0 < R) :
    0 < modularMcShaneRivinLatticeCount R := by
  rw [modularMcShaneRivinLatticeCount_eq_coordinate_ncard,
    Set.ncard_eq_toFinset_card _ (modularMcShaneRivinCoordinateSet_finite R hR)]
  apply Finset.card_pos.mpr
  refine ⟨(0, 0), ?_⟩
  simpa only [Set.Finite.mem_toFinset] using t1_geometric_zero_mem R hR

/-- The scalar-image equality is proved on the actual finite point sets. -/
theorem t1_geometric_divisor_fiber_image (R : ℝ) (hR : 0 < R) (g : ℕ) (hg : 0 < g) :
    (t1_geometricNonzeroFinset (R / g) (div_pos hR (by exact_mod_cast hg))).image
        (fun p => g • p) =
      (t1_geometricNonzeroFinset R hR).filter (fun p => g ∣ Int.gcd p.1 p.2) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  ext p
  simp only [Finset.mem_image, Finset.mem_filter, t1_mem_geometricNonzeroFinset]
  constructor
  · rintro ⟨q, ⟨hq, hqR⟩, rfl⟩
    have hqnorm := (t1_mem_coordinate_norm_iff (R / g) (div_pos hR hgR) q).mp hqR
    refine ⟨⟨t1_integer_nsmul_ne_zero g hg hq, ?_⟩, ?_⟩
    · apply (t1_mem_coordinate_norm_iff R hR (g • q)).mpr
      rw [t1_intrinsic_norm_nsmul]
      nlinarith [(le_div_iff₀ hgR).mp hqnorm]
    · exact (t1_integer_gcd_dvd_iff_nsmul g (g • q)).mpr ⟨q, rfl⟩
  · rintro ⟨⟨hp, hpR⟩, hdiv⟩
    obtain ⟨q, rfl⟩ := (t1_integer_gcd_dvd_iff_nsmul g p).mp hdiv
    refine ⟨q, ⟨?_, ?_⟩, rfl⟩
    · intro hq
      apply hp
      rw [hq]
      ext <;> simp
    · apply (t1_mem_coordinate_norm_iff (R / g) (div_pos hR hgR) q).mpr
      apply (le_div_iff₀ hgR).mpr
      have hpbound := (t1_mem_coordinate_norm_iff R hR (g • q)).mp hpR
      rw [t1_intrinsic_norm_nsmul] at hpbound
      nlinarith

theorem t1_geometric_divisor_fiber_card (R : ℝ) (hR : 0 < R) (g : ℕ) (hg : 0 < g) :
    ((t1_geometricNonzeroFinset R hR).filter (fun p => g ∣ Int.gcd p.1 p.2)).card =
      (t1_geometricNonzeroFinset (R / g) (div_pos hR (by exact_mod_cast hg))).card := by
  rw [← t1_geometric_divisor_fiber_image R hR g hg]
  exact Finset.card_image_of_injective _ (t1_integer_nsmul_injective g hg)

/-- Exact geometric Möbius inversion, with a computed finite cutoff and
the radius R/g in the true original marked lattice. -/
theorem t1_geometricPrimitiveCount_moebius_scaled (R : ℝ) (hR : 0 < R) :
    (t1_geometricPrimitiveCount R : ℤ) =
      ∑ g ∈ Finset.Icc 1 (t1_gcdCutoff (t1_geometricNonzeroFinset R hR)),
        μ g * if hg : 0 < g then
          ((t1_geometricNonzeroFinset (R / g)
            (div_pos hR (by exact_mod_cast hg))).card : ℤ) else 0 := by
  rw [t1_geometricPrimitiveCount_moebius_fibers R hR]
  apply Finset.sum_congr rfl
  intro g hg
  have hgpos : 0 < g := (Finset.mem_Icc.mp hg).1
  rw [dif_pos hgpos, t1_geometric_divisor_fiber_card R hR g hgpos]

/-- The paper's finite Möbius inversion formula with the origin removed
from the actual full geometric lattice count. -/
theorem t1_geometricPrimitiveCount_moebius_full (R : ℝ) (hR : 0 < R) :
    (t1_geometricPrimitiveCount R : ℤ) =
      ∑ g ∈ Finset.Icc 1 (t1_gcdCutoff (t1_geometricNonzeroFinset R hR)),
        μ g * ((modularMcShaneRivinLatticeCount (R / g) - 1 : ℕ) : ℤ) := by
  rw [t1_geometricPrimitiveCount_moebius_scaled R hR]
  apply Finset.sum_congr rfl
  intro g hg
  have hgpos : 0 < g := (Finset.mem_Icc.mp hg).1
  rw [dif_pos hgpos, t1_geometricNonzero_card (R / g)
    (div_pos hR (by exact_mod_cast hgpos))]

end Markov
