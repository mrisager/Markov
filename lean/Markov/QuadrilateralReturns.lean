import Markov.QuadrilateralReturnEnumeration

noncomputable section
open scoped MatrixGroups
namespace Markov

theorem paperQuadrilateralCoverWords_mem_iff (g : SL(2, ℤ)) :
    g ∈ paperQuadrilateralCoverWords ↔
      ∃ i : Fin 10, paperQuadrilateralCoverWordAt i = g := by
  classical
  simp [paperQuadrilateralCoverWords, paperQuadrilateralUpperWords,
    Fin.exists_fin_succ, paperQuadrilateralCoverWordAt, eq_comm, mul_assoc]
  tauto

theorem paperIdealQuadrilateral_index_coverage (z : UpperHalfPlane)
    (hz : z ∈ paperIdealQuadrilateral) :
    ∃ i : Fin 10, ∃ u ∈ ModularGroup.fd, z = paperQuadrilateralCoverWordAt i • u := by
  obtain ⟨g, hg, u, hu, hact⟩ := paperIdealQuadrilateral_finite_word_coverage z hz
  obtain ⟨i, rfl⟩ := (paperQuadrilateralCoverWords_mem_iff g).mp hg
  exact ⟨i, u, hu, hact⟩

theorem paperQuadrilateralCoverWordAt_eq_cutWord (i : Fin 10) :
    ∃ left : Bool, paperQuadrilateralCoverWordAt i =
      paperQuadrilateralCutWord (paperQuadrilateralCoverResidue i) left := by
  fin_cases i
  · exact ⟨true, rfl⟩
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩
  · exact ⟨true, rfl⟩
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

theorem paperQuadrilateralCoverWordAt_quotient (i : Fin 10) :
    modularTraceProjectiveQuotientMap (paperQuadrilateralCoverWordAt i) =
      modularTraceProjectiveQuotientT ^ (paperQuadrilateralCoverResidue i).val := by
  obtain ⟨left, h⟩ := paperQuadrilateralCoverWordAt_eq_cutWord i
  rw [h]
  exact paperQuadrilateralCutWord_quotient _ _

private theorem paperQuadrilateral_SL_mul_neg (a b : SL(2, ℤ)) : a * (-b) = -(a * b) := by
  apply Subtype.ext
  change (a : Matrix (Fin 2) (Fin 2) ℤ) * -(b : Matrix (Fin 2) (Fin 2) ℤ) =
    -((a : Matrix (Fin 2) (Fin 2) ℤ) * (b : Matrix (Fin 2) (Fin 2) ℤ))
  exact mul_neg _ _

private theorem paperQuadrilateral_SL_neg_mul (a b : SL(2, ℤ)) : (-a) * b = -(a * b) := by
  apply Subtype.ext
  change -(a : Matrix (Fin 2) (Fin 2) ℤ) * (b : Matrix (Fin 2) (Fin 2) ℤ) =
    -((a : Matrix (Fin 2) (Fin 2) ℤ) * (b : Matrix (Fin 2) (Fin 2) ℤ))
  exact neg_mul _ _

theorem paperIdealQuadrilateral_signed_return_candidate (g : SL(2, ℤ))
    (hg : g ∈ modularTraceSubgroup) (z : UpperHalfPlane)
    (hz : z ∈ paperIdealQuadrilateral) (hgz : g • z ∈ paperIdealQuadrilateral) :
    ∃ l : Fin 9, g = paperQuadrilateralReturnCandidateAt l ∨
      g = -paperQuadrilateralReturnCandidateAt l := by
  obtain ⟨i, u, hu, hzu⟩ := paperIdealQuadrilateral_index_coverage z hz
  obtain ⟨j, v, hv, hgv⟩ := paperIdealQuadrilateral_index_coverage (g • z) hgz
  let a : SL(2, ℤ) := (paperQuadrilateralCoverWordAt j)⁻¹ * g *
    paperQuadrilateralCoverWordAt i
  have hact : a • u = v := by
    dsimp only [a]
    rw [mul_smul, mul_smul, ← hzu, hgv, inv_smul_smul]
  have hret : a • u ∈ ModularGroup.fd := hact.symm ▸ hv
  obtain ⟨h, hh, hah, _⟩ := (modularClosedDomain_signed_return_iff a u hu).mp hret
  obtain ⟨k, rfl⟩ := (modularClosedReturnWords_mem_iff h).mp hh
  have hlabel : modularTraceProjectiveQuotientMap a =
      (modularTraceProjectiveQuotientT ^ (paperQuadrilateralCoverResidue j).val)⁻¹ *
        modularTraceProjectiveQuotientT ^ (paperQuadrilateralCoverResidue i).val := by
    dsimp only [a]
    rw [map_mul, map_mul, map_inv,
      paperQuadrilateralCoverWordAt_quotient, paperQuadrilateralCoverWordAt_quotient]
    rw [modularTraceProjectiveQuotientMap_subgroup ⟨g, hg⟩, mul_one]
  have hlabel' : modularTraceProjectiveQuotientMap (modularClosedReturnWordAt k) =
      (modularTraceProjectiveQuotientT ^ (paperQuadrilateralCoverResidue j).val)⁻¹ *
        modularTraceProjectiveQuotientT ^ (paperQuadrilateralCoverResidue i).val := by
    rcases hah with ha | ha
    · rwa [ha] at hlabel
    · rwa [ha, modularTraceProjectiveQuotientMap_neg] at hlabel
  have hres : ((paperQuadrilateralCoverResidue j).val +
      (modularClosedReturnResidue k).val) % 6 = (paperQuadrilateralCoverResidue i).val := by
    apply (modularTraceSixCell_label_pow_iff
      (paperQuadrilateralCoverResidue i) (paperQuadrilateralCoverResidue j) _).mp
    exact (modularClosedReturnWordAt_quotient k).symm.trans hlabel'
  obtain ⟨l, hl⟩ := paperQuadrilateralReturn_finite_enumeration i j k hres
  have hgprod : g = paperQuadrilateralCoverWordAt j * a *
      (paperQuadrilateralCoverWordAt i)⁻¹ := by dsimp only [a]; group
  refine ⟨l, ?_⟩
  rcases hah with ha | ha
  · rw [ha] at hgprod
    exact hl.imp (hgprod.trans ·) (hgprod.trans ·)
  · have hgprod' : g = -(paperQuadrilateralCoverWordAt j * modularClosedReturnWordAt k *
        (paperQuadrilateralCoverWordAt i)⁻¹) := by
      rw [hgprod, ha, paperQuadrilateral_SL_mul_neg, paperQuadrilateral_SL_neg_mul]
    rcases hl with hl | hl
    · exact Or.inr (hgprod'.trans (congrArg Neg.neg hl))
    · exact Or.inl (by simpa only [neg_neg] using hgprod'.trans (congrArg Neg.neg hl))

end Markov

