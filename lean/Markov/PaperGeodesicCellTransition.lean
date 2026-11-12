import Markov.PaperGeodesicSideCrossing

/-! An actual noncoincident isometric line meeting an original side passes
between the two actual neighboring cell interiors. The parameter radius and
the either/or orientation are constructed from continuity and proved signs. -/
noncomputable section
open Set Topology
namespace Markov

/-- Genuine local cell transition at an actual original-side crossing. There
is no transversality or transition hypothesis: actual metric straightening,
side signs, actual closed-cell adjacency and continuity produce the radius. -/
theorem paperQuadrilateral_isometric_side_cell_transition
    (F : ℝ → UpperHalfPlane) (hF : Isometry F) (k : Fin 4)
    (hne : Set.range F ≠ paperQuadrilateralGeodesicSide k)
    (t₀ : ℝ) (hroot : F t₀ ∈ paperQuadrilateralGeodesicSide k) :
    ∃ ε > 0,
      ((∀ t ∈ Ioo (t₀-ε) t₀, F t ∈ interior paperIdealQuadrilateral) ∧
        (∀ t ∈ Ioo t₀ (t₀+ε), F t ∈
          (fun z : UpperHalfPlane => paperQuadrilateralSideNeighbor k • z) ''
            interior paperIdealQuadrilateral)) ∨
      ((∀ t ∈ Ioo (t₀-ε) t₀, F t ∈
          (fun z : UpperHalfPlane => paperQuadrilateralSideNeighbor k • z) ''
            interior paperIdealQuadrilateral) ∧
        (∀ t ∈ Ioo t₀ (t₀+ε), F t ∈ interior paperIdealQuadrilateral)) := by
  obtain ⟨U, hU, hrootU, hpos, hneg⟩ :=
    paperQuadrilateral_side_local_strict_halfplanes k (F t₀) hroot
  have hpre : {t : ℝ | F t ∈ U} ∈ 𝓝 t₀ :=
    hF.continuous.continuousAt (hU.mem_nhds hrootU)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hpre
  have hnear (t : ℝ) (ht : t ∈ Ioo (t₀-ε) (t₀+ε)) : F t ∈ U := by
    apply hεU
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  let l := t₀-ε/2
  let r := t₀+ε/2
  have hl : l < t₀ := by dsimp [l]; linarith
  have hr : t₀ < r := by dsimp [r]; linarith
  have hprod := paperQuadrilateralSideFunction_isometric_crossing F hF k hne t₀ hroot l r hl hr
  rcases mul_neg_iff.mp hprod with ⟨hlpos, hrneg⟩ | ⟨hlneg, hrpos⟩
  · refine ⟨ε, hε, Or.inl ⟨?_, ?_⟩⟩
    · intro t ht
      apply hpos (F t) (hnear t ⟨ht.1, by linarith [ht.2]⟩)
      have hp := paperQuadrilateralSideFunction_isometric_crossing F hF k hne t₀ hroot t r ht.2 hr
      nlinarith only [hp, hrneg]
    · intro t ht
      apply hneg (F t) (hnear t ⟨by linarith [ht.1], ht.2⟩)
      have hp := paperQuadrilateralSideFunction_isometric_crossing F hF k hne t₀ hroot l t hl ht.1
      nlinarith only [hp, hlpos]
  · refine ⟨ε, hε, Or.inr ⟨?_, ?_⟩⟩
    · intro t ht
      apply hneg (F t) (hnear t ⟨ht.1, by linarith [ht.2]⟩)
      have hp := paperQuadrilateralSideFunction_isometric_crossing F hF k hne t₀ hroot t r ht.2 hr
      nlinarith only [hp, hrpos]
    · intro t ht
      apply hpos (F t) (hnear t ⟨by linarith [ht.1], ht.2⟩)
      have hp := paperQuadrilateralSideFunction_isometric_crossing F hF k hne t₀ hroot l t hl ht.1
      nlinarith only [hp, hlneg]

private theorem cellTransition_translate_mem
    (δ : modularTraceSubgroup) (S : Set UpperHalfPlane) (z : UpperHalfPlane)
    (hz : δ⁻¹ • z ∈ S) : z ∈ (fun w : UpperHalfPlane => δ • w) '' S :=
  ⟨δ⁻¹ • z, hz, smul_inv_smul _ _⟩

private theorem cellTransition_translate_neighbor_mem
    (δ η : modularTraceSubgroup) (S : Set UpperHalfPlane) (z : UpperHalfPlane)
    (hz : δ⁻¹ • z ∈ (fun w : UpperHalfPlane => η • w) '' S) :
    z ∈ (fun w : UpperHalfPlane => (δ * η) • w) '' S := by
  obtain ⟨w, hw, hweq⟩ := hz
  change η • w = δ⁻¹ • z at hweq
  refine ⟨w, hw, ?_⟩
  change (δ * η) • w = z
  rw [mul_smul, hweq, smul_inv_smul]

/-- Every actual hyperbolic deck axis crossing an actual translated original
side has a positive parameter radius and crosses between exactly the original
δ-cell interior and the literal δ*neighbor(k)-cell interior, in either orientation. -/
theorem modularHyperbolicAxis_paper_side_cell_transition
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (δ : modularTraceSubgroup) (k : Fin 4) (t₀ v₀ : ℝ)
    (hpoint : modularHyperbolicAxis g hg t₀ = δ • paperQuadrilateralGeodesicSideLine k v₀) :
    ∃ ε > 0,
      ((∀ t ∈ Ioo (t₀-ε) t₀, modularHyperbolicAxis g hg t ∈
          (fun z : UpperHalfPlane => δ • z) '' interior paperIdealQuadrilateral) ∧
        (∀ t ∈ Ioo t₀ (t₀+ε), modularHyperbolicAxis g hg t ∈
          (fun z : UpperHalfPlane => (δ * paperQuadrilateralSideNeighbor k) • z) ''
            interior paperIdealQuadrilateral)) ∨
      ((∀ t ∈ Ioo (t₀-ε) t₀, modularHyperbolicAxis g hg t ∈
          (fun z : UpperHalfPlane => (δ * paperQuadrilateralSideNeighbor k) • z) ''
            interior paperIdealQuadrilateral) ∧
        (∀ t ∈ Ioo t₀ (t₀+ε), modularHyperbolicAxis g hg t ∈
          (fun z : UpperHalfPlane => δ • z) '' interior paperIdealQuadrilateral)) := by
  let F : ℝ → UpperHalfPlane := fun t => δ⁻¹ • modularHyperbolicAxis g hg t
  have hF : Isometry F :=
    (modularSubgroup_isometry modularTraceSubgroup δ⁻¹).comp (modularHyperbolicAxis_isometry g hg)
  have hne : Set.range F ≠ paperQuadrilateralGeodesicSide k := by
    intro he
    apply modularHyperbolicAxis_ne_translated_paper_side_range g hg δ k
    rw [paperQuadrilateralGeodesicSideLine_translate_range, ← he, ← Set.range_comp']
    simp only [F, smul_inv_smul]
  have hroot : F t₀ ∈ paperQuadrilateralGeodesicSide k := by
    change δ⁻¹ • modularHyperbolicAxis g hg t₀ ∈ paperQuadrilateralGeodesicSide k
    rw [hpoint, inv_smul_smul, ← paperQuadrilateralGeodesicSideLine_range]
    exact ⟨v₀, rfl⟩
  obtain ⟨ε, hε, hcases⟩ := paperQuadrilateral_isometric_side_cell_transition F hF k hne t₀ hroot
  refine ⟨ε, hε, ?_⟩
  rcases hcases with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · left
    constructor
    · intro t ht
      exact cellTransition_translate_mem δ _ _ (hl t ht)
    · intro t ht
      exact cellTransition_translate_neighbor_mem δ (paperQuadrilateralSideNeighbor k) _ _ (hr t ht)
  · right
    constructor
    · intro t ht
      exact cellTransition_translate_neighbor_mem δ (paperQuadrilateralSideNeighbor k) _ _ (hl t ht)
    · intro t ht
      exact cellTransition_translate_mem δ _ _ (hr t ht)

end Markov
