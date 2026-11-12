import Markov.PaperQuadrilateralCutWords
import Markov.PaperQuadrilateralFiniteCover
import Markov.ModularSixCellProper

/-! Properness and the actual kernel quotient of the literal paper quadrilateral.
No identification of the kernel with the A/B side-generated relation, or of
this quotient with a topological punctured torus, is asserted. -/
noncomputable section
open scoped MatrixGroups
open Set Topology
namespace Markov

/-- The translated quotient distance controls the original coordinate height.
Only integral modularity of the conjugated deck transform is needed. -/
theorem modularTrace_im_le_exp_translated_quotient_dist
    (g : SL(2, ℤ)) (w : UpperHalfPlane) :
    w.im ≤ Real.exp (dist (modularTraceQuotientMk (g • w))
      (modularTraceQuotientMk (g • UpperHalfPlane.I))) := by
  obtain ⟨γ, hγ⟩ := modularTraceQuotient_dist_attained (g • w) (g • UpperHalfPlane.I)
  let a : SL(2, ℤ) := g⁻¹ * γ.val * g
  have hγ' : dist (modularTraceQuotientMk (g • w))
      (modularTraceQuotientMk (g • UpperHalfPlane.I)) =
      dist (g • w) (γ.val • (g • UpperHalfPlane.I)) := hγ
  have hd : dist (g • w) (γ.val • (g • UpperHalfPlane.I)) =
      dist w (a • UpperHalfPlane.I) := by
    calc
      dist (g • w) (γ.val • (g • UpperHalfPlane.I)) =
          dist (g⁻¹ • (g • w)) (g⁻¹ • (γ.val • (g • UpperHalfPlane.I))) :=
        ((modularInteger_isometry g⁻¹).dist_eq _ _).symm
      _ = dist w (a • UpperHalfPlane.I) := by
        dsimp only [a]
        rw [inv_smul_smul, mul_smul, mul_smul]
  rw [hγ', hd]
  calc
    w.im ≤ (a • UpperHalfPlane.I).im * Real.exp (dist w (a • UpperHalfPlane.I)) :=
      UpperHalfPlane.im_le_im_mul_exp_dist w (a • UpperHalfPlane.I)
    _ ≤ 1 * Real.exp (dist w (a • UpperHalfPlane.I)) :=
      mul_le_mul_of_nonneg_right (modularIntegral_smul_I_im_le_one a)
        (Real.exp_pos _).le
    _ = Real.exp (dist w (a • UpperHalfPlane.I)) := one_mul _

/-- A fixed quotient ball gives a uniform height cap in each fixed integral
coordinate chart, with its explicit translated basepoint distance. -/
theorem modularTrace_im_le_exp_of_translated_quotient_dist_le
    (g : SL(2, ℤ)) (w : UpperHalfPlane) (R : ℝ)
    (hR : dist (modularTraceQuotientMk (g • w))
      (modularTraceQuotientMk UpperHalfPlane.I) ≤ R) :
    w.im ≤ Real.exp (R + dist (modularTraceQuotientMk UpperHalfPlane.I)
      (modularTraceQuotientMk (g • UpperHalfPlane.I))) := by
  apply (modularTrace_im_le_exp_translated_quotient_dist g w).trans
  apply Real.exp_le_exp.mpr
  exact (dist_triangle _ (modularTraceQuotientMk UpperHalfPlane.I) _).trans
    (add_le_add hR le_rfl)


/-- The actual restriction of the existing orbit projection to the literal Q. -/
def paperQuadrilateralQuotientMap (z : paperIdealQuadrilateral) : ModularTraceQuotient :=
  modularTraceQuotientMk z.val

theorem paperQuadrilateralQuotientMap_continuous : Continuous paperQuadrilateralQuotientMap :=
  modularTraceQuotientMk_continuous.comp continuous_subtype_val

theorem paperQuadrilateralQuotientMap_surjective :
    Function.Surjective paperQuadrilateralQuotientMap := by
  intro x
  obtain ⟨z, hz, heq⟩ := paperIdealQuadrilateral_quotient_coverage x
  exact ⟨⟨z, hz⟩, heq⟩

/-- The finite actual-word cover and translated quotient-distance height bounds
make the full Q-restriction compact over every compact subset downstairs. -/
theorem paperQuadrilateralQuotientMap_isCompact_preimage
    (K : Set ModularTraceQuotient) (hK : IsCompact K) :
    IsCompact (paperQuadrilateralQuotientMap ⁻¹' K) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall
    (modularTraceQuotientMk UpperHalfPlane.I)
  let cap (g : SL(2, ℤ)) : Set UpperHalfPlane :=
    {w | w ∈ ModularGroup.fd ∧ w.im ≤ Real.exp
      (R + dist (modularTraceQuotientMk UpperHalfPlane.I)
        (modularTraceQuotientMk (g • UpperHalfPlane.I)))}
  have hcap (g : SL(2, ℤ)) : IsCompact (cap g) :=
    modularStandardCell_im_le_isCompact _
  have hc : IsCompact (⋃ g ∈ paperQuadrilateralCoverWords,
      (fun w : UpperHalfPlane => g • w) '' cap g) := by
    apply Finset.isCompact_biUnion
    intro g _
    exact (hcap g).image (modularInteger_isometry g).continuous
  have hambient : IsCompact {z : UpperHalfPlane |
      z ∈ paperIdealQuadrilateral ∧ modularTraceQuotientMk z ∈ K} := by
    apply hc.of_isClosed_subset
      (paperIdealQuadrilateral_isClosed.inter
        (hK.isClosed.preimage modularTraceQuotientMk_continuous))
    intro z hz
    obtain ⟨g, hg, w, hw, hact⟩ := paperIdealQuadrilateral_finite_word_coverage z hz.1
    refine mem_iUnion₂.mpr ⟨g, hg, w, ⟨hw, ?_⟩, hact.symm⟩
    apply modularTrace_im_le_exp_of_translated_quotient_dist_le
    rw [← hact]
    exact hR hz.2
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  convert hambient using 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hz, hKz⟩
    exact ⟨⟨z, hz⟩, hKz, rfl⟩

/-- The literal paper quadrilateral projection is an actual proper map. -/
theorem paperQuadrilateralQuotientMap_isProperMap :
    IsProperMap paperQuadrilateralQuotientMap := by
  apply isProperMap_iff_isCompact_preimage.mpr
  exact ⟨paperQuadrilateralQuotientMap_continuous,
    fun {_} hK => paperQuadrilateralQuotientMap_isCompact_preimage _ hK⟩

/-- Its proved coverage and properness give the quotient-map property. -/
theorem paperQuadrilateralQuotientMap_isQuotientMap :
    IsQuotientMap paperQuadrilateralQuotientMap := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨paperQuadrilateralQuotientMap_surjective, fun K => ?_⟩
  constructor
  · exact fun hK => hK.preimage paperQuadrilateralQuotientMap_continuous
  · intro hK
    have hc := paperQuadrilateralQuotientMap_isProperMap.isClosedMap
      (paperQuadrilateralQuotientMap ⁻¹' K) hK
    simpa only [image_preimage_eq K paperQuadrilateralQuotientMap_surjective] using hc

/-- The literal Q is divided by its actual orbit-projection kernel. An A/B
side-pairing presentation of this relation is a separate theorem. -/
def paperQuadrilateralBoundarySetoid : Setoid paperIdealQuadrilateral :=
  Setoid.ker paperQuadrilateralQuotientMap

theorem paperQuadrilateralBoundarySetoid_iff (z w : paperIdealQuadrilateral) :
    paperQuadrilateralBoundarySetoid z w ↔
      ∃ g : modularTraceSubgroup, g • w.val = z.val :=
  modularTraceQuotientMk_eq_iff z.val w.val

abbrev PaperQuadrilateralKernelQuotient := Quotient paperQuadrilateralBoundarySetoid

/-- The actual kernel quotient of the literal Q, with quotient topology, is
homeomorphic to the existing trace orbit quotient with its original topology. -/
def paperQuadrilateralKernelQuotientHomeomorph :
    PaperQuadrilateralKernelQuotient ≃ₜ ModularTraceQuotient :=
  (show IsQuotientMap
    (⟨paperQuadrilateralQuotientMap, paperQuadrilateralQuotientMap_continuous⟩ :
      C(paperIdealQuadrilateral, ModularTraceQuotient)) from
        paperQuadrilateralQuotientMap_isQuotientMap).homeomorph

@[simp] theorem paperQuadrilateralKernelQuotientHomeomorph_mk
    (z : paperIdealQuadrilateral) :
    paperQuadrilateralKernelQuotientHomeomorph (Quotient.mk _ z) =
      modularTraceQuotientMk z.val := rfl

end Markov
