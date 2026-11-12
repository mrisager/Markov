import T1MertensFinite
import T1GeometricThreshold

/-! The actual finite hyperbola identity for the geometric Möbius tail.
The Mertens function is the genuine arithmetic sum, and all point sets,
lengths, integer floors, and divisor cutoffs are constructed definitions. -/

noncomputable section
open Classical Finset Set
open scoped ArithmeticFunction.Moebius
namespace Markov

theorem t1_geometric_threshold_fiber (R : ℝ) (hR : 0 < R) (D g : ℕ)
    (hD : 0 < D) (hDg : D ≤ g) :
    t1_geometricNonzeroFinset (R / g) (div_pos hR (by exact_mod_cast hD.trans_le hDg)) =
      (t1_geometricNonzeroFinset (R / D) (div_pos hR (by exact_mod_cast hD))).filter
        (fun p => g ≤ t1_geometricThreshold R p) := by
  have hg : 0 < g := hD.trans_le hDg
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hcompare : R / g ≤ R / D := by
    apply (div_le_div_iff₀ hgR hDR).mpr
    have hDgR : (D : ℝ) ≤ g := by exact_mod_cast hDg
    nlinarith
  ext p
  simp only [Finset.mem_filter, t1_mem_geometricNonzeroFinset]
  constructor
  · rintro ⟨hp, hpg⟩
    refine ⟨⟨hp, ?_⟩, (t1_geometricThreshold_iff R hR g hg p hp).mpr hpg⟩
    apply (t1_mem_coordinate_norm_iff (R / D) (div_pos hR hDR) p).mpr
    exact ((t1_mem_coordinate_norm_iff (R / g) (div_pos hR hgR) p).mp hpg).trans hcompare
  · rintro ⟨⟨hp, _⟩, ht⟩
    exact ⟨hp, (t1_geometricThreshold_iff R hR g hg p hp).mp ht⟩

/-- If the chosen divisor cutoff exceeds the computed maximum gcd, then
the corresponding small-radius nonzero point set is actually empty. -/
theorem t1_geometric_small_radius_empty (R : ℝ) (hR : 0 < R) (D : ℕ) (hD : 0 < D)
    (hlarge : t1_gcdCutoff (t1_geometricNonzeroFinset R hR) < D) :
    t1_geometricNonzeroFinset (R / D) (div_pos hR (by exact_mod_cast hD)) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hne, hmem⟩ := (t1_mem_geometricNonzeroFinset _ _ p).mp hp
  have hDT := (t1_geometricThreshold_iff R hR D hD p hne).mpr hmem
  have hTB := t1_geometricThreshold_le_cutoff R hR p hne
  omega

/-- Exact finite hyperbola identity on the original marked geometric
lattice. It includes the empty-tail regime and points on the Y=R/D boundary.
No Mertens cancellation estimate or counting-model hypothesis is used. -/
theorem t1_geometric_mobius_tail_hyperbola (R : ℝ) (hR : 0 < R) (D : ℕ) (hD : 0 < D) :
    (∑ g ∈ Finset.Ioc D (t1_gcdCutoff (t1_geometricNonzeroFinset R hR)),
      μ g * ((modularMcShaneRivinLatticeCount (R / g) - 1 : ℕ) : ℤ)) =
      ∑ p ∈ t1_geometricNonzeroFinset (R / D) (div_pos hR (by exact_mod_cast hD)),
        (t1_mertensNat (t1_geometricThreshold R p) - t1_mertensNat D) := by
  by_cases hDB : D ≤ t1_gcdCutoff (t1_geometricNonzeroFinset R hR)
  · calc
      _ = ∑ g ∈ Finset.Ioc D (t1_gcdCutoff (t1_geometricNonzeroFinset R hR)),
          μ g * (((t1_geometricNonzeroFinset (R / D)
            (div_pos hR (by exact_mod_cast hD))).filter
              (fun p => g ≤ t1_geometricThreshold R p)).card : ℤ) := by
        apply Finset.sum_congr rfl
        intro g hg
        have hDg := (Finset.mem_Ioc.mp hg).1
        have hgpos : 0 < g := hD.trans hDg
        rw [← t1_geometricNonzero_card (R / g) (div_pos hR (by exact_mod_cast hgpos)),
          t1_geometric_threshold_fiber R hR D g hD hDg.le]
      _ = ∑ p ∈ t1_geometricNonzeroFinset (R / D) (div_pos hR (by exact_mod_cast hD)),
          (t1_mertensNat (min (t1_gcdCutoff (t1_geometricNonzeroFinset R hR))
            (t1_geometricThreshold R p)) - t1_mertensNat (min D (t1_geometricThreshold R p))) :=
        t1_finite_hyperbola_interchange (α := ℤ × ℤ)
          (t1_geometricNonzeroFinset (R / D) (div_pos hR (by exact_mod_cast hD)))
          (t1_geometricThreshold R) D
          (t1_gcdCutoff (t1_geometricNonzeroFinset R hR)) hDB
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        obtain ⟨hne, hmem⟩ := (t1_mem_geometricNonzeroFinset _ _ p).mp hp
        have hDT := (t1_geometricThreshold_iff R hR D hD p hne).mpr hmem
        have hTB := t1_geometricThreshold_le_cutoff R hR p hne
        rw [min_eq_right hTB, min_eq_left hDT]
  · have hBD := Nat.lt_of_not_ge hDB
    rw [t1_geometric_small_radius_empty R hR D hD hBD]
    have hinterval : Finset.Ioc D (t1_gcdCutoff (t1_geometricNonzeroFinset R hR)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro g hg
      have := Finset.mem_Ioc.mp hg
      omega
    simp only [hinterval, Finset.sum_empty]

end Markov
