import Markov.HyperbolicDiagonalization
import Markov.HyperbolicDiagonalMinset

/-! Actual minimizing loci and uniqueness for invariant isometric hyperbolic
axes. Negative SL representatives are reduced by their proved identical action.
No local-geodesic straightening or simplicity is asserted. -/

noncomputable section
open Set
open scoped MatrixGroups
namespace Markov

/-- Every actual hyperbolic SL action admits a positive diagonal action
conjugacy, retaining the metric translation length and either central sign. -/
theorem exists_hyperbolicPositiveDiagonal_action_conjugacy
    (g : SL(2, ℝ)) (hg : 2 < |(g : Matrix (Fin 2) (Fin 2) ℝ).trace|) :
    ∃ a : ℝ, ∃ ha : 1 < a, ∃ h : SL(2, ℝ),
      (∀ z : UpperHalfPlane, g • z =
        h • (hyperbolicPositiveDiagonal a (by linarith) • (h⁻¹ • z))) ∧
      hyperbolicTranslationLength g = 2 * Real.log a := by
  rcases lt_abs.mp hg with hp | hn
  · obtain ⟨a, ha, h, hh⟩ := exists_hyperbolicPositiveDiagonal_conjugacy g hp
    refine ⟨a, ha, h, ?_, ?_⟩
    · intro z
      rw [hh]
      simp only [mul_smul]
    · rw [hh, hyperbolicTranslationLength_conjugate,
        hyperbolicTranslationLength_positiveDiagonal a ha]
  · have hn' : 2 < ((-g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace := by
      simpa only [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg] using hn
    obtain ⟨a, ha, h, hh⟩ := exists_hyperbolicPositiveDiagonal_conjugacy (-g) hn'
    refine ⟨a, ha, h, ?_, ?_⟩
    · intro z
      rw [← hyperbolic_neg_smul g z, hh]
      simp only [mul_smul]
    · rw [← hyperbolicTranslationLength_neg g, hh,
        hyperbolicTranslationLength_conjugate,
        hyperbolicTranslationLength_positiveDiagonal a ha]

/-- In a genuine diagonalizing coordinate, the actual minimizing points are
exactly the points with zero real part. -/
theorem hyperbolicTranslationLength_minimizer_iff_of_diagonal_action
    (g : SL(2, ℝ)) (a : ℝ) (ha : 1 < a) (h : SL(2, ℝ))
    (hact : ∀ z : UpperHalfPlane, g • z =
      h • (hyperbolicPositiveDiagonal a (by linarith) • (h⁻¹ • z)))
    (hlen : hyperbolicTranslationLength g = 2 * Real.log a) (z : UpperHalfPlane) :
    dist z (g • z) = hyperbolicTranslationLength g ↔ (h⁻¹ • z).re = 0 := by
  have hd : dist z (g • z) = dist (h⁻¹ • z)
      (hyperbolicPositiveDiagonal a (by linarith) • (h⁻¹ • z)) := by
    rw [hact z]
    simpa only [smul_inv_smul] using dist_smul h (h⁻¹ • z)
      (hyperbolicPositiveDiagonal a (by linarith) • (h⁻¹ • z))
  rw [hd, hlen]
  exact hyperbolicPositiveDiagonal_displacement_eq_iff a ha (h⁻¹ • z)

/-- Every actual invariant isometric axis has the explicit conjugate-vertical
formula, with its positive orientation and parameter shift retained. -/
theorem hyperbolicTranslationLength_invariantAxis_eq_of_diagonal_action
    (g : SL(2, ℝ)) (a : ℝ) (ha : 1 < a) (h : SL(2, ℝ))
    (hact : ∀ z : UpperHalfPlane, g • z =
      h • (hyperbolicPositiveDiagonal a (by linarith) • (h⁻¹ • z)))
    (hlen : hyperbolicTranslationLength g = 2 * Real.log a)
    (γ : ℝ → UpperHalfPlane) (hγ : Isometry γ)
    (hγact : ∀ t : ℝ, g • γ t = γ (t + hyperbolicTranslationLength g)) :
    ∃ c : ℝ, ∀ t : ℝ, γ t = h • hyperbolicVerticalAxis (t + c) := by
  let δ : ℝ → UpperHalfPlane := fun t => h⁻¹ • γ t
  have hδ : Isometry δ := (isometry_smul UpperHalfPlane h⁻¹).comp hγ
  have hδact (t : ℝ) : hyperbolicPositiveDiagonal a (by linarith) • δ t =
      δ (t + 2 * Real.log a) := by
    have he := congrArg (fun z : UpperHalfPlane => h⁻¹ • z) (hγact t)
    rw [hact (γ t), hlen] at he
    simpa only [inv_smul_smul] using he
  obtain ⟨c, hc⟩ := hyperbolicPositiveDiagonal_invariantAxis_eq a ha δ hδ hδact
  refine ⟨c, ?_⟩
  intro t
  have he := congrArg (fun z : UpperHalfPlane => h • z) (hc t)
  simpa only [δ, smul_inv_smul] using he

/-- For every actual hyperbolic matrix, the complete displacement-minimizing
locus is the range of any of its positively invariant isometric axes. -/
theorem hyperbolicTranslationLength_minimizingLocus_eq_axis_range
    (g : SL(2, ℝ)) (hg : 2 < |(g : Matrix (Fin 2) (Fin 2) ℝ).trace|)
    (γ : ℝ → UpperHalfPlane) (hγ : Isometry γ)
    (hγact : ∀ t : ℝ, g • γ t = γ (t + hyperbolicTranslationLength g)) :
    {z : UpperHalfPlane | dist z (g • z) = hyperbolicTranslationLength g} =
      Set.range γ := by
  obtain ⟨a, ha, h, hact, hlen⟩ :=
    exists_hyperbolicPositiveDiagonal_action_conjugacy g hg
  obtain ⟨c, hc⟩ := hyperbolicTranslationLength_invariantAxis_eq_of_diagonal_action
    g a ha h hact hlen γ hγ hγact
  ext z
  rw [Set.mem_setOf_eq,
    hyperbolicTranslationLength_minimizer_iff_of_diagonal_action g a ha h hact hlen]
  constructor
  · intro hz
    refine ⟨Real.log (h⁻¹ • z).im - c, ?_⟩
    rw [hc, sub_add_cancel]
    have he : hyperbolicVerticalAxis (Real.log (h⁻¹ • z).im) = h⁻¹ • z := by
      apply UpperHalfPlane.ext_re_im
      · simpa only [hyperbolicVerticalAxis, UpperHalfPlane.mk_re, Complex.zero_re] using hz.symm
      · exact Real.exp_log (h⁻¹ • z).im_pos
    rw [he, smul_inv_smul]
  · rintro ⟨t, rfl⟩
    rw [hc, inv_smul_smul]
    rfl

/-- Any two actual positively invariant unit-speed hyperbolic axes differ by
a real parameter shift. No claim about arbitrary local geodesics is used. -/
theorem hyperbolicTranslationLength_invariantAxis_eq
    (g : SL(2, ℝ)) (hg : 2 < |(g : Matrix (Fin 2) (Fin 2) ℝ).trace|)
    (γ δ : ℝ → UpperHalfPlane) (hγ : Isometry γ) (hδ : Isometry δ)
    (hγact : ∀ t : ℝ, g • γ t = γ (t + hyperbolicTranslationLength g))
    (hδact : ∀ t : ℝ, g • δ t = δ (t + hyperbolicTranslationLength g)) :
    ∃ c : ℝ, ∀ t : ℝ, γ t = δ (t + c) := by
  obtain ⟨a, ha, h, hact, hlen⟩ :=
    exists_hyperbolicPositiveDiagonal_action_conjugacy g hg
  obtain ⟨cγ, hcγ⟩ := hyperbolicTranslationLength_invariantAxis_eq_of_diagonal_action
    g a ha h hact hlen γ hγ hγact
  obtain ⟨cδ, hcδ⟩ := hyperbolicTranslationLength_invariantAxis_eq_of_diagonal_action
    g a ha h hact hlen δ hδ hδact
  refine ⟨cγ - cδ, ?_⟩
  intro t
  rw [hcγ, hcδ]
  congr 2
  ring

/-- The actual range of a hyperbolic invariant isometric axis is unique. -/
theorem hyperbolicTranslationLength_invariantAxis_range_unique
    (g : SL(2, ℝ)) (hg : 2 < |(g : Matrix (Fin 2) (Fin 2) ℝ).trace|)
    (γ δ : ℝ → UpperHalfPlane) (hγ : Isometry γ) (hδ : Isometry δ)
    (hγact : ∀ t : ℝ, g • γ t = γ (t + hyperbolicTranslationLength g))
    (hδact : ∀ t : ℝ, g • δ t = δ (t + hyperbolicTranslationLength g)) :
    Set.range γ = Set.range δ := by
  rw [← hyperbolicTranslationLength_minimizingLocus_eq_axis_range g hg γ hγ hγact,
    hyperbolicTranslationLength_minimizingLocus_eq_axis_range g hg δ hδ hδact]

end Markov
