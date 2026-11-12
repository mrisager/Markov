import Markov.PaperQuadrilateralUpperCover

/-! A finite actual-word cover of the literal paper quadrilateral. -/
noncomputable section
open scoped MatrixGroups
namespace Markov

/-- The five actual words covering the part above the unit semicircle. -/
def paperQuadrilateralUpperWords : Finset SL(2, ℤ) := by
  classical
  exact {1, ModularGroup.T, ModularGroup.T⁻¹, ModularGroup.T * ModularGroup.S,
    ModularGroup.T⁻¹ * ModularGroup.S}

/-- The ten actual words obtained by retaining the upper pieces and their S-images. -/
def paperQuadrilateralCoverWords : Finset SL(2, ℤ) := by
  classical
  exact paperQuadrilateralUpperWords ∪
    paperQuadrilateralUpperWords.image (fun g => ModularGroup.S * g)

theorem paperIdealQuadrilateral_upper_word_coverage (z : UpperHalfPlane)
    (hQ : z ∈ paperIdealQuadrilateral) (hN : 1 ≤ Complex.normSq (z : ℂ)) :
    ∃ g ∈ paperQuadrilateralUpperWords, ∃ w ∈ ModularGroup.fd, z = g • w := by
  classical
  obtain ⟨w, hw, h⟩ := paperIdealQuadrilateral_upper_coverage z hQ hN
  rcases h with h | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact ⟨1, by simp [paperQuadrilateralUpperWords], w, hw, by simpa only [one_smul] using h⟩
  · exact ⟨ModularGroup.T, by simp [paperQuadrilateralUpperWords], w, hw, h⟩
  · exact ⟨ModularGroup.T⁻¹, by simp [paperQuadrilateralUpperWords], w, hw, h⟩
  · exact ⟨ModularGroup.T * ModularGroup.S,
      by simp [paperQuadrilateralUpperWords], w, hw, h⟩
  · exact ⟨ModularGroup.T⁻¹ * ModularGroup.S,
      by simp [paperQuadrilateralUpperWords], w, hw, h⟩

/-- Every point of the literal paper quadrilateral is in one of the ten
actual standard-cell images. The half-cell conditions are retained in the
stronger upper-coverage theorem; this finite cover suffices for compactness. -/
theorem paperIdealQuadrilateral_finite_word_coverage (z : UpperHalfPlane)
    (hQ : z ∈ paperIdealQuadrilateral) :
    ∃ g ∈ paperQuadrilateralCoverWords, ∃ w ∈ ModularGroup.fd, z = g • w := by
  classical
  by_cases hN : 1 ≤ Complex.normSq (z : ℂ)
  · obtain ⟨g, hg, w, hw, hact⟩ := paperIdealQuadrilateral_upper_word_coverage z hQ hN
    exact ⟨g, Finset.mem_union_left _ hg, w, hw, hact⟩
  · have hSQ : ModularGroup.S • z ∈ paperIdealQuadrilateral :=
      (paperIdealQuadrilateral_S_mem_iff z).mpr hQ
    have hSN : 1 ≤ Complex.normSq ((ModularGroup.S • z : UpperHalfPlane) : ℂ) := by
      rw [modular_normSq_S_smul, ← one_div]
      apply (le_div_iff₀ z.normSq_pos).mpr
      simpa only [one_mul] using (le_of_not_ge hN)
    obtain ⟨g, hg, w, hw, hact⟩ :=
      paperIdealQuadrilateral_upper_word_coverage (ModularGroup.S • z) hSQ hSN
    refine ⟨ModularGroup.S * g,
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g, hg, rfl⟩), w, hw, ?_⟩
    rw [mul_smul, ← hact, modular_S_smul_involutive]

end Markov
