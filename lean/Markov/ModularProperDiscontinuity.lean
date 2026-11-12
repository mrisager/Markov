import Markov.ModularTraceQuotient
import Mathlib.NumberTheory.Modular
import Mathlib.Topology.Algebra.ProperAction.ProperlyDiscontinuous

/-! Proper discontinuity of the actual integral modular action. The proof
uses properness of the integer bottom-row map and of the remaining row
coordinate, then the actual hyperbolic isometries and compact balls. -/

noncomputable section
open scoped MatrixGroups
open Filter Set UpperHalfPlane
namespace Markov

/-- A bounded real part and an imaginary part bounded away from zero leave
only finitely many integral modular matrices moving a fixed point there. -/
theorem modularInteger_finite_preimage_verticalStrip (z : UpperHalfPlane)
    (A B : ℝ) (hB : 0 < B) :
    {g : SL(2, ℤ) | g • z ∈ verticalStrip A B}.Finite := by
  have hrows : {p : Fin 2 → ℤ |
      Complex.normSq ((p 0 : ℂ) * z + p 1) ≤ z.im / B}.Finite := by
    simpa only [not_lt] using Filter.eventually_cofinite.mp
      ((ModularGroup.tendsto_normSq_coprime_pair z).eventually
        (eventually_gt_atTop (z.im / B)))
  apply Set.Finite.of_finite_fibers (fun g : SL(2, ℤ) => g 1)
  · apply hrows.subset
    rintro p ⟨g, hg, rfl⟩
    have him := hg.2
    rw [ModularGroup.im_smul_eq_div_normSq] at him
    change B ≤ z.im / Complex.normSq ((g 1 0 : ℂ) * z + g 1 1) at him
    have hpos : 0 < Complex.normSq ((g 1 0 : ℂ) * z + g 1 1) := by
      exact UpperHalfPlane.normSq_denom_pos (g : GL (Fin 2) ℝ) z.im_ne_zero
    apply (le_div_iff₀ hB).mpr
    have := (le_div_iff₀ hpos).mp him
    nlinarith
  · rintro p ⟨g₀, _, hg₀⟩
    have hp : IsCoprime (p 0) (p 1) := by
      rw [← hg₀]
      exact ModularGroup.bottom_row_coprime g₀
    have hf : {g : {g : SL(2, ℤ) // g 1 = p} |
        |((g : SL(2, ℤ)) • z).re| ≤ A}.Finite := by
      simpa only [not_lt] using Filter.eventually_cofinite.mp
        ((ModularGroup.tendsto_abs_re_smul z hp).eventually (eventually_gt_atTop A))
    apply (hf.image Subtype.val).subset
    intro g hg
    exact ⟨⟨g, hg.2⟩, hg.1.1, rfl⟩

theorem modularInteger_finite_preimage_compact (z : UpperHalfPlane)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    {g : SL(2, ℤ) | g • z ∈ K}.Finite := by
  obtain ⟨A, B, hB, hKB⟩ := subset_verticalStrip_of_isCompact hK
  exact (modularInteger_finite_preimage_verticalStrip z A B hB).subset
    (fun _ hg => hKB hg)

/-- Proper discontinuity is proved for the full actual integral modular
action, so finite stabilizers are allowed here. -/
instance modularInteger_properlyDiscontinuousSMul :
    ProperlyDiscontinuousSMul SL(2, ℤ) UpperHalfPlane where
  finite_disjoint_inter_image {K L} hK hL := by
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall UpperHalfPlane.I
    obtain ⟨s, hs⟩ := hL.isBounded.subset_closedBall UpperHalfPlane.I
    apply (modularInteger_finite_preimage_compact UpperHalfPlane.I
      (isCompact_closedBall UpperHalfPlane.I (r + s))).subset
    rintro g ⟨_, ⟨z, hz, rfl⟩, hgz⟩
    change dist (g • UpperHalfPlane.I) UpperHalfPlane.I ≤ r + s
    calc
      dist (g • UpperHalfPlane.I) UpperHalfPlane.I ≤
          dist (g • UpperHalfPlane.I) (g • z) + dist (g • z) UpperHalfPlane.I :=
        dist_triangle _ _ _
      _ = dist UpperHalfPlane.I z + dist (g • z) UpperHalfPlane.I := by
        rw [(modularInteger_isometry g).dist_eq]
      _ ≤ r + s := add_le_add (by simpa only [dist_comm] using hr hz) (hs hgz)

instance modularSubgroup_properlyDiscontinuousSMul (Γ : Subgroup SL(2, ℤ)) :
    ProperlyDiscontinuousSMul Γ UpperHalfPlane where
  finite_disjoint_inter_image {K L} hK hL := by
    have hfinite : {g : SL(2, ℤ) | ((g • ·) '' K ∩ L).Nonempty}.Finite :=
      finite_disjoint_inter_image hK hL
    exact Set.Finite.preimage (f := fun g : Γ => g.val)
      Subtype.val_injective.injOn hfinite

theorem modularTraceQuotient_isT2 : T2Space ModularTraceQuotient := by
  letI : DiscreteTopology modularTraceSubgroup := inferInstance
  letI : ProperSMul modularTraceSubgroup UpperHalfPlane :=
    (properlyDiscontinuousSMul_iff_properSMul).mp inferInstance
  infer_instance

end Markov
