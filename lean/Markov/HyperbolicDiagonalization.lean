import Markov.HyperbolicTranslationLength

/-! Actual special-linear diagonalization of real hyperbolic matrices.
The conjugator is constructed from eigenvectors and normalized to determinant
one by rescaling one column. No diagonalization hypothesis is postulated. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

private theorem exists_SL_diagonal_conjugacy_of_intertwiner
    (g : SL(2, ℝ)) (r : ℝ) (hr : 0 < r)
    (P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.det ≠ 0)
    (hinter : (g : Matrix (Fin 2) (Fin 2) ℝ) * P =
      P * (hyperbolicPositiveDiagonal r hr : Matrix (Fin 2) (Fin 2) ℝ)) :
    ∃ h : SL(2, ℝ), g = h * hyperbolicPositiveDiagonal r hr * h⁻¹ := by
  let E : Matrix (Fin 2) (Fin 2) ℝ := !![P.det⁻¹, 0; 0, 1]
  have hdet : (P * E).det = 1 := by
    rw [Matrix.det_mul]
    have he : E.det = P.det⁻¹ := by simp [E, Matrix.det_fin_two]
    rw [he]
    exact mul_inv_cancel₀ hP
  let h : SL(2, ℝ) := ⟨P * E, hdet⟩
  refine ⟨h, ?_⟩
  have hcomm : (hyperbolicPositiveDiagonal r hr : Matrix (Fin 2) (Fin 2) ℝ) * E =
      E * (hyperbolicPositiveDiagonal r hr : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hyperbolicPositiveDiagonal, E, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) ℝ) * (P * E) =
    (P * E) * (hyperbolicPositiveDiagonal r hr : Matrix (Fin 2) (Fin 2) ℝ)
  rw [← Matrix.mul_assoc, hinter, Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc]

/-- A determinant-one real matrix with trace `r+r⁻¹`, `r>1`, is actually
conjugate in SL(2,R) to the positive diagonal with entries `r,r⁻¹`. -/
theorem exists_hyperbolicPositiveDiagonal_conjugacy_of_trace
    (g : SL(2, ℝ)) (r : ℝ) (hr : 1 < r)
    (htrace : (g : Matrix (Fin 2) (Fin 2) ℝ).trace = r + r⁻¹) :
    ∃ h : SL(2, ℝ), g = h * hyperbolicPositiveDiagonal r (by linarith) * h⁻¹ := by
  let a := g 0 0
  let b := g 0 1
  let c := g 1 0
  let d := g 1 1
  have hr0 : 0 < r := by linarith
  have hri : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
  have hneq : r ≠ r⁻¹ := by
    have hh : r⁻¹ < 1 := (inv_lt_one₀ hr0).mpr hr
    linarith
  have ht : a + d = r + r⁻¹ := by
    simpa only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] using htrace
  have hd : a * d - b * c = 1 := by simpa only [Matrix.det_fin_two] using g.property
  have hrchar : r ^ 2 - (a + d) * r + 1 = 0 := by
    have hh := congrArg (fun x : ℝ => x * r) ht
    dsimp only at hh
    nlinarith [hri]
  have hichar : (r⁻¹) ^ 2 - (a + d) * r⁻¹ + 1 = 0 := by
    have hh := congrArg (fun x : ℝ => x * r⁻¹) ht
    dsimp only at hh
    nlinarith [hri]
  by_cases hc : c = 0
  · by_cases hb : b = 0
    · have hroot : (a - r) * (a - r⁻¹) = 0 := by
        have hdet : a * d = 1 := by simpa only [hc, mul_zero, sub_zero] using hd
        have hh := congrArg (fun x : ℝ => a * x) ht
        dsimp only at hh
        nlinarith [hri]
      rcases mul_eq_zero.mp hroot with ha | ha
      · have ha' : a = r := sub_eq_zero.mp ha
        have hd' : d = r⁻¹ := by linarith
        refine ⟨1, ?_⟩
        simp only [one_mul, inv_one, mul_one]
        apply Subtype.ext
        dsimp only [a, b, c, d] at ha' hd' hc hb
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [hyperbolicPositiveDiagonal, ha', hd', hc, hb]
      · have ha' : a = r⁻¹ := sub_eq_zero.mp ha
        have hd' : d = r := by linarith
        let h : SL(2, ℝ) := ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two]⟩
        refine ⟨h, ?_⟩
        apply Subtype.ext
        dsimp only [a, b, c, d] at ha' hd' hc hb
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [h, hyperbolicPositiveDiagonal, Matrix.SpecialLinearGroup.coe_inv,
            Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
            ha', hd', hc, hb]
    · let P : Matrix (Fin 2) (Fin 2) ℝ := !![b, b; r - a, r⁻¹ - a]
      have hP : P.det ≠ 0 := by
        have heq : P.det = b * (r⁻¹ - r) := by simp [P, Matrix.det_fin_two]; ring
        rw [heq]
        exact mul_ne_zero hb (sub_ne_zero.mpr hneq.symm)
      apply exists_SL_diagonal_conjugacy_of_intertwiner g r hr0 P hP
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [P, hyperbolicPositiveDiagonal, Matrix.mul_apply, Fin.sum_univ_two]
      all_goals dsimp only [a, b, c, d] at ht hd hc hb hrchar hichar ⊢
      all_goals nlinarith [hri, hrchar, hichar]
  · let P : Matrix (Fin 2) (Fin 2) ℝ := !![r - d, r⁻¹ - d; c, c]
    have hP : P.det ≠ 0 := by
      have heq : P.det = c * (r - r⁻¹) := by simp [P, Matrix.det_fin_two]; ring
      rw [heq]
      exact mul_ne_zero hc (sub_ne_zero.mpr hneq)
    apply exists_SL_diagonal_conjugacy_of_intertwiner g r hr0 P hP
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, hyperbolicPositiveDiagonal, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals dsimp only [a, b, c, d] at ht hd hc hrchar hichar ⊢
    all_goals nlinarith [hri, hrchar, hichar]

/-- Positive hyperbolic trace supplies actual expanding and contracting
eigenvalues and a determinant-one eigenbasis. -/
theorem exists_hyperbolicPositiveDiagonal_conjugacy
    (g : SL(2, ℝ)) (hg : 2 < (g : Matrix (Fin 2) (Fin 2) ℝ).trace) :
    ∃ r : ℝ, ∃ hr : 1 < r, ∃ h : SL(2, ℝ),
      g = h * hyperbolicPositiveDiagonal r (by linarith) * h⁻¹ := by
  let t := (g : Matrix (Fin 2) (Fin 2) ℝ).trace / 2
  have ht : 1 < t := by dsimp [t]; linarith
  let r := Real.exp (Real.arcosh t)
  have hr : 1 < r := by
    simpa only [r, Real.exp_zero] using Real.exp_lt_exp.mpr (Real.arcosh_pos ht)
  have htrace : (g : Matrix (Fin 2) (Fin 2) ℝ).trace = r + r⁻¹ := by
    have hh := Real.cosh_arcosh ht.le
    rw [Real.cosh_eq, Real.exp_neg] at hh
    dsimp only [r, t] at hh ⊢
    linarith
  obtain ⟨h, hh⟩ := exists_hyperbolicPositiveDiagonal_conjugacy_of_trace g r hr htrace
  exact ⟨r, hr, h, hh⟩

/-- For every actual positive-trace hyperbolic matrix, the metric
displacement infimum equals the standard hyperbolic trace formula. -/
theorem hyperbolicTranslationLength_trace_of_trace_gt_two
    (g : SL(2, ℝ)) (hg : 2 < (g : Matrix (Fin 2) (Fin 2) ℝ).trace) :
    hyperbolicTranslationLength g =
      2 * Real.arcosh (|(g : Matrix (Fin 2) (Fin 2) ℝ).trace| / 2) := by
  obtain ⟨r, hr, h, hh⟩ := exists_hyperbolicPositiveDiagonal_conjugacy g hg
  exact hyperbolicTranslationLength_trace_of_diagonal_conjugacy g h r hr hh

/-- The genuine metric translation-length infimum of every positive-trace
hyperbolic matrix is attained on a conjugate vertical axis. -/
theorem hyperbolicTranslationLength_attained_of_trace_gt_two
    (g : SL(2, ℝ)) (hg : 2 < (g : Matrix (Fin 2) (Fin 2) ℝ).trace) :
    ∃ z : UpperHalfPlane, dist z (g • z) = hyperbolicTranslationLength g := by
  obtain ⟨r, hr, h, hh⟩ := exists_hyperbolicPositiveDiagonal_conjugacy g hg
  exact hyperbolicTranslationLength_attained_of_diagonal_conjugacy g h r hr hh

/-- Opposite determinant-one representatives act identically on the actual
upper half-plane, as required when passing from SL to PSL. -/
theorem hyperbolic_neg_smul (g : SL(2, ℝ)) (z : UpperHalfPlane) :
    (-g) • z = g • z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
  change ((-((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) : ℝ) * (z : ℂ) +
      (-((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) : ℝ)) /
    ((-((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) : ℝ) * (z : ℂ) +
      (-((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) : ℝ)) = _
  simp only [Complex.ofReal_neg, neg_mul, ← neg_add, neg_div_neg_eq,
    Algebra.algebraMap_self, RingHom.id_apply]

/-- The metric displacement infimum is independent of the SL central sign. -/
theorem hyperbolicTranslationLength_neg (g : SL(2, ℝ)) :
    hyperbolicTranslationLength (-g) = hyperbolicTranslationLength g := by
  unfold hyperbolicTranslationLength
  simp only [hyperbolic_neg_smul]

/-- Unconditional metric trace-length formula for every genuine real
hyperbolic determinant-one matrix, including negative traces. -/
theorem hyperbolicTranslationLength_trace
    (g : SL(2, ℝ)) (hg : 2 < |(g : Matrix (Fin 2) (Fin 2) ℝ).trace|) :
    hyperbolicTranslationLength g =
      2 * Real.arcosh (|(g : Matrix (Fin 2) (Fin 2) ℝ).trace| / 2) := by
  rcases lt_abs.mp hg with hp | hn
  · exact hyperbolicTranslationLength_trace_of_trace_gt_two g hp
  · have hn' : 2 < ((-g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace := by
      simpa only [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg] using hn
    have hh := hyperbolicTranslationLength_trace_of_trace_gt_two (-g) hn'
    simpa only [hyperbolicTranslationLength_neg, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.trace_neg, abs_neg] using hh

/-- Hyperbolicity gives a strictly positive actual metric translation length. -/
theorem hyperbolicTranslationLength_pos
    (g : SL(2, ℝ)) (hg : 2 < |(g : Matrix (Fin 2) (Fin 2) ℝ).trace|) :
    0 < hyperbolicTranslationLength g := by
  rw [hyperbolicTranslationLength_trace g hg]
  exact mul_pos (by norm_num) (Real.arcosh_pos (by linarith))

/-- Every genuine hyperbolic determinant-one matrix attains its actual
metric translation length; no diagonalization premise remains. -/
theorem hyperbolicTranslationLength_attained
    (g : SL(2, ℝ)) (hg : 2 < |(g : Matrix (Fin 2) (Fin 2) ℝ).trace|) :
    ∃ z : UpperHalfPlane, dist z (g • z) = hyperbolicTranslationLength g := by
  rcases lt_abs.mp hg with hp | hn
  · exact hyperbolicTranslationLength_attained_of_trace_gt_two g hp
  · have hn' : 2 < ((-g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace := by
      simpa only [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg] using hn
    obtain ⟨z, hz⟩ := hyperbolicTranslationLength_attained_of_trace_gt_two (-g) hn'
    exact ⟨z, by simpa only [hyperbolic_neg_smul, hyperbolicTranslationLength_neg] using hz⟩

/-- Every positive-trace hyperbolic matrix translates an actual unit-speed
hyperbolic line by its metric translation length. -/
theorem hyperbolicTranslationLength_axis_of_trace_gt_two
    (g : SL(2, ℝ)) (hg : 2 < (g : Matrix (Fin 2) (Fin 2) ℝ).trace) :
    ∃ γ : ℝ → UpperHalfPlane, Isometry γ ∧
      ∀ t : ℝ, g • γ t = γ (t + hyperbolicTranslationLength g) := by
  obtain ⟨r, hr, h, hh⟩ := exists_hyperbolicPositiveDiagonal_conjugacy g hg
  refine ⟨fun t => h • hyperbolicVerticalAxis t, ?_, ?_⟩
  · apply Isometry.of_dist_eq
    intro s t
    rw [dist_smul]
    exact hyperbolicVerticalAxis_isometry.dist_eq s t
  · intro t
    rw [hh, hyperbolicTranslationLength_conjugate, hyperbolicTranslationLength_positiveDiagonal r hr]
    simpa only [mul_smul, inv_smul_smul] using
      congrArg (fun z : UpperHalfPlane => h • z)
        (hyperbolicPositiveDiagonal_axis_action r (by linarith) t)

/-- The actual invariant unit-speed axis exists for either hyperbolic SL
representative; the central sign has no effect on the hyperbolic geometry. -/
theorem hyperbolicTranslationLength_axis
    (g : SL(2, ℝ)) (hg : 2 < |(g : Matrix (Fin 2) (Fin 2) ℝ).trace|) :
    ∃ γ : ℝ → UpperHalfPlane, Isometry γ ∧
      ∀ t : ℝ, g • γ t = γ (t + hyperbolicTranslationLength g) := by
  rcases lt_abs.mp hg with hp | hn
  · exact hyperbolicTranslationLength_axis_of_trace_gt_two g hp
  · have hn' : 2 < ((-g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace := by
      simpa only [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg] using hn
    obtain ⟨γ, hγ, heq⟩ := hyperbolicTranslationLength_axis_of_trace_gt_two (-g) hn'
    refine ⟨γ, hγ, ?_⟩
    intro t
    simpa only [hyperbolic_neg_smul, hyperbolicTranslationLength_neg] using heq t

end Markov
