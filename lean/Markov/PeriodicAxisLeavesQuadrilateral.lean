import Markov.PaperQuadrilateralLocalFiniteness

/-! No actual isometric real line whose quotient projection has positive
period can be contained in one full closed quadrilateral translate. The proof
uses the actual compact return fibre, not an ideal-endpoint classification. -/

noncomputable section
open Set Topology
namespace Markov

/-- A positive periodic projected isometric line must leave every single
closed original quadrilateral translate. No simplicity premise is used. -/
theorem periodicIsometricLine_not_contained_quadrilateral_translate
    (F : ℝ → UpperHalfPlane) (hF : Isometry F) (L : ℝ) (hL : 0 < L)
    (hperiod : Function.Periodic (fun t => modularTraceQuotientMk (F t)) L)
    (δ : modularTraceSubgroup) :
    ¬ Set.range F ⊆ (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral := by
  intro hsub
  let R : Set UpperHalfPlane := {z | z ∈ paperIdealQuadrilateral ∧
    modularTraceQuotientMk z ∈ modularTraceQuotientMk '' ({F 0} : Set UpperHalfPlane)}
  have hR : IsCompact R := paperIdealQuadrilateral_compact_over_compact_image
    {F 0} isCompact_singleton
  have hπ (n : ℕ) : modularTraceQuotientMk (F ((n : ℝ)*L)) =
      modularTraceQuotientMk (F 0) := by
    induction n with
    | zero => simp
    | succ n ih =>
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
        (hperiod ((n : ℝ)*L)).trans ih
  have hmem (n : ℕ) : F ((n : ℝ)*L) ∈ (fun z : UpperHalfPlane => δ • z) '' R := by
    obtain ⟨z, hz, heq⟩ := hsub ⟨(n : ℝ)*L, rfl⟩
    refine ⟨z, ⟨hz, ?_⟩, heq⟩
    refine ⟨F 0, rfl, ?_⟩
    exact ((modularTraceQuotientMk_smul δ z).symm.trans
      (congrArg modularTraceQuotientMk heq)).trans (hπ n) |>.symm
  obtain ⟨C, hC⟩ := (hR.image (modularTraceSubgroup_isometry δ).continuous).isBounded.subset_closedBall (F 0)
  obtain ⟨n, hn⟩ := exists_nat_gt (C/L)
  have hlt : C < (n : ℝ)*L := (div_lt_iff₀ hL).mp hn
  have hle := hC (hmem n)
  change dist (F ((n : ℝ)*L)) (F 0) ≤ C at hle
  rw [hF.dist_eq, Real.dist_eq, sub_zero,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hL.le)] at hle
  exact (not_le_of_gt hlt) hle

/-- In particular every actual hyperbolic deck-axis crosses out of every
single full closed quadrilateral translate. Coincident-edge cases therefore
cannot be supplied silently in a finite normal-arc construction. -/
theorem modularHyperbolicAxis_not_contained_quadrilateral_translate
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (δ : modularTraceSubgroup) :
    ¬ Set.range (modularHyperbolicAxis g hg) ⊆
      (fun z : UpperHalfPlane => δ • z) '' paperIdealQuadrilateral :=
  periodicIsometricLine_not_contained_quadrilateral_translate
    (modularHyperbolicAxis g hg) (modularHyperbolicAxis_isometry g hg)
    (modularClosedGeodesicPeriod g) (modularClosedGeodesicPeriod_pos g hg)
    (modularClosedGeodesic_periodic g hg) δ

end Markov
