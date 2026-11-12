import Markov.HyperbolicTranslationLength

/-! The actual displacement-minimizing set of a positive hyperbolic diagonal.
This proves no simplicity or local-geodesic straightening assertion. -/

noncomputable section
open Set
open scoped MatrixGroups
namespace Markov

/-- Equality in the actual diagonal displacement lower bound holds exactly
on the imaginary axis. -/
theorem hyperbolicPositiveDiagonal_displacement_eq_iff
    (a : ℝ) (ha : 1 < a) (z : UpperHalfPlane) :
    dist z (hyperbolicPositiveDiagonal a (by linarith) • z) =
      2 * Real.log a ↔ z.re = 0 := by
  have ha0 : 0 < a := by linarith
  let v := hyperbolicVerticalAxis (Real.log z.im)
  have hvre : v.re = 0 := rfl
  have hvim : v.im = z.im := by
    dsimp [v, hyperbolicVerticalAxis]
    exact Real.exp_log z.im_pos
  constructor
  · intro h
    have hc : Real.cosh (dist z (hyperbolicPositiveDiagonal a (by linarith) • z)) =
        Real.cosh (dist v (hyperbolicPositiveDiagonal a (by linarith) • v)) := by
      rw [h, hyperbolicPositiveDiagonal_axis_displacement a ha]
    rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist',
      hyperbolicPositiveDiagonal_re, hyperbolicPositiveDiagonal_im,
      hyperbolicPositiveDiagonal_re, hyperbolicPositiveDiagonal_im, hvre, hvim] at hc
    have hden : 2 * z.im * (a ^ 2 * z.im) ≠ 0 := by positivity
    have hn := (div_left_inj' hden).mp hc
    have ha2 : 1 < a ^ 2 := by nlinarith
    have hzsq : (z.re - a ^ 2 * z.re) ^ 2 = 0 := by nlinarith
    have hz : z.re - a ^ 2 * z.re = 0 := sq_eq_zero_iff.mp hzsq
    nlinarith
  · intro hz
    have hzv : z = v := UpperHalfPlane.ext_re_im (hz.trans hvre.symm) hvim.symm
    rw [hzv]
    exact hyperbolicPositiveDiagonal_axis_displacement a ha (Real.log z.im)

/-- The complete actual displacement-minimizing locus of the positive diagonal
is precisely the range of the existing unit-speed vertical axis. -/
theorem hyperbolicPositiveDiagonal_minimizingLocus
    (a : ℝ) (ha : 1 < a) :
    {z : UpperHalfPlane |
      dist z (hyperbolicPositiveDiagonal a (by linarith) • z) =
        hyperbolicTranslationLength (hyperbolicPositiveDiagonal a (by linarith))} =
      Set.range hyperbolicVerticalAxis := by
  ext z
  rw [Set.mem_setOf_eq, hyperbolicTranslationLength_positiveDiagonal a ha,
    hyperbolicPositiveDiagonal_displacement_eq_iff a ha]
  constructor
  · intro hz
    refine ⟨Real.log z.im, ?_⟩
    apply UpperHalfPlane.ext_re_im
    · simpa [hyperbolicVerticalAxis] using hz.symm
    · exact Real.exp_log z.im_pos
  · rintro ⟨t, rfl⟩
    rfl

/-- Every actual invariant unit-speed diagonal axis with the positive
translation parameter is the existing vertical axis up to a parameter shift. -/
theorem hyperbolicPositiveDiagonal_invariantAxis_eq
    (a : ℝ) (ha : 1 < a) (γ : ℝ → UpperHalfPlane) (hγ : Isometry γ)
    (hact : ∀ t : ℝ, hyperbolicPositiveDiagonal a (by linarith) • γ t =
      γ (t + 2 * Real.log a)) :
    ∃ c : ℝ, ∀ t : ℝ, γ t = hyperbolicVerticalAxis (t + c) := by
  have ha0 : 0 < a := by linarith
  have hL : 0 < 2 * Real.log a := mul_pos (by norm_num) (Real.log_pos ha)
  have hre (t : ℝ) : (γ t).re = 0 := by
    apply (hyperbolicPositiveDiagonal_displacement_eq_iff a ha (γ t)).mp
    rw [hact, hγ.dist_eq, Real.dist_eq]
    have he : t - (t + 2 * Real.log a) = -(2 * Real.log a) := by ring
    rw [he, abs_neg, abs_of_pos hL]
  let f : ℝ → ℝ := fun t => Real.log (γ t).im
  have hf (s t : ℝ) : dist (f s) (f t) = dist s t := by
    rw [← UpperHalfPlane.dist_of_re_eq ((hre s).trans (hre t).symm), hγ.dist_eq]
  have hfL : f (2 * Real.log a) = f 0 + 2 * Real.log a := by
    have he := congrArg UpperHalfPlane.im (hact 0)
    rw [zero_add, hyperbolicPositiveDiagonal_im] at he
    dsimp only [f]
    rw [← he, Real.log_mul (pow_ne_zero 2 ha0.ne') (γ 0).im_ne_zero,
      Real.log_pow]
    ring
  have hfeq (t : ℝ) : f t = t + f 0 := by
    have h0 := congrArg (fun x : ℝ => x ^ 2) (hf t 0)
    have h1 := congrArg (fun x : ℝ => x ^ 2) (hf t (2 * Real.log a))
    simp only [Real.dist_eq, sq_abs, sub_zero] at h0 h1
    rw [hfL] at h1
    nlinarith
  refine ⟨f 0, ?_⟩
  intro t
  apply UpperHalfPlane.ext_re_im
  · exact hre t
  · change (γ t).im = Real.exp (t + f 0)
    rw [← hfeq t]
    exact (Real.exp_log (γ t).im_pos).symm

/-- In particular, invariant isometric diagonal axes have the same actual
range. This does not assert that arbitrary local geodesics are global axes. -/
theorem hyperbolicPositiveDiagonal_invariantAxis_range
    (a : ℝ) (ha : 1 < a) (γ : ℝ → UpperHalfPlane) (hγ : Isometry γ)
    (hact : ∀ t : ℝ, hyperbolicPositiveDiagonal a (by linarith) • γ t =
      γ (t + 2 * Real.log a)) :
    Set.range γ = Set.range hyperbolicVerticalAxis := by
  obtain ⟨c, hc⟩ := hyperbolicPositiveDiagonal_invariantAxis_eq a ha γ hγ hact
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t + c, (hc t).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t - c, by simpa using hc (t - c)⟩

end Markov
