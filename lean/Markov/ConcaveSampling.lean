import Markov.ConcaveSamplingFiniteMesh
import Markov.ConcaveSamplingIntegerMesh

/-! V1 Lemma 9, with the paper's shifted integer mesh and coefficient 7.
Nonnegativity follows from concavity and the endpoint values forced by
continuity, so no additional sign hypothesis is necessary. -/

noncomputable section
open Set MeasureTheory
namespace Markov

theorem concave_sampling_lemma9 {f : ℝ → ℝ} (hc : Continuous f)
    (hf : ConcaveOn ℝ (Icc 0 1) f)
    (hz : ∀ x, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    {h : ℝ} (hh : 0 < h) (hhsmall : h < 1 / 8) (y : ℝ) :
    |h * (∑' n : ℤ, f (h * ((n : ℝ) + y))) - ∫ x, f x| ≤
      7 * h * (f h + f (1 - h)) := by
  obtain ⟨h0, h1⟩ := continuous_zero_off_unit_endpoints hc hz
  obtain ⟨N, u, hN, hu, hlast, hsum⟩ :=
    exists_integer_sampling_mesh hz hh hhsmall y
  rw [hsum, continuous_zero_off_unit_integral hc hz]
  exact concave_sampling_finite_mesh_bound hf hc.continuousOn h0 h1
    hh hhsmall hN hu hlast

theorem concave_sampling_lemma9_with_summability {f : ℝ → ℝ} (hc : Continuous f)
    (hf : ConcaveOn ℝ (Icc 0 1) f)
    (hz : ∀ x, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    {h : ℝ} (hh : 0 < h) (hhsmall : h < 1 / 8) (y : ℝ) :
    Summable (fun n : ℤ => f (h * ((n : ℝ) + y))) ∧
      |h * (∑' n : ℤ, f (h * ((n : ℝ) + y))) - ∫ x, f x| ≤
        7 * h * (f h + f (1 - h)) :=
  ⟨sampling_summable hz hh y, concave_sampling_lemma9 hc hf hz hh hhsmall y⟩

end Markov
