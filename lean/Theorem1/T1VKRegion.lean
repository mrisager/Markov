import T1VKHeightWidth
import T1RieszKernelInversion
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Topology.MetricSpace.Thickening

/-! A literal high-height Vinogradov–Korobov zero-free region is the
explicit premise. The compact-height part is proved from Mathlib's
actual nonvanishing on Re=1, including the removed pole. -/
noncomputable section
open Set Complex Metric
namespace Markov

def t1_VKZeroFreeRegion : Prop :=
  ∃ c T : ℝ, 0 < c ∧ 4 ≤ T ∧
    ∀ s : ℂ, T ≤ |s.im| → 1-t1_vkHeightWidth c s.im ≤ s.re → riemannZeta s ≠ 0

theorem t1_poleRemovedZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    t1_poleRemovedZeta s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hn
  · simp [t1_poleRemovedZeta]
  · simpa only [t1_poleRemovedZeta,Function.update_of_ne hn] using
      mul_ne_zero (sub_ne_zero.mpr hn) (riemannZeta_ne_zero_of_one_le_re hs)

theorem t1_verticalPoint_distance (s : ℂ) (σ : ℝ) :
    dist s (t1_verticalPoint σ s.im) = |s.re-σ| := by
  rw [dist_eq_norm]
  have he : s-t1_verticalPoint σ s.im = ((s.re-σ : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re,t1_verticalPoint_re,Complex.ofReal_re]
    · simp only [Complex.sub_im,t1_verticalPoint_im,sub_self,Complex.ofReal_im]
  rw [he,Complex.norm_real,Real.norm_eq_abs]

theorem t1_poleRemovedZeta_compact_height (T : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℂ, |s.im| ≤ T → 1-ε ≤ s.re → t1_poleRemovedZeta s ≠ 0 := by
  let K := (t1_verticalPoint 1) '' Icc (-T) T
  let U := {s : ℂ | t1_poleRemovedZeta s ≠ 0}
  have hK : IsCompact K := isCompact_Icc.image (t1_verticalPoint_continuous 1)
  have hU : IsOpen U := isOpen_ne_fun t1_poleRemovedZeta_differentiable.continuous continuous_const
  have hKU : K ⊆ U := by
    rintro s ⟨t,_,rfl⟩
    exact t1_poleRemovedZeta_ne_zero_of_one_le_re (by rw [t1_verticalPoint_re])
  obtain ⟨r,hr,hsub⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨r/2,by positivity,?_⟩
  intro s ht hs
  by_cases h : 1 ≤ s.re
  · exact t1_poleRemovedZeta_ne_zero_of_one_le_re h
  have hdist : dist s (t1_verticalPoint 1 s.im) < r := by
    rw [t1_verticalPoint_distance,abs_of_nonpos (by linarith : s.re-1 ≤ 0)]
    linarith
  exact hsub (Metric.mem_thickening_iff.mpr
    ⟨t1_verticalPoint 1 s.im,⟨s.im,abs_le.mp ht,rfl⟩,hdist⟩)

theorem t1_VKZeroFreeRegion_global (h : t1_VKZeroFreeRegion) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1/4 ∧
      ∀ s : ℂ, 1-t1_vkHeightWidth c s.im ≤ s.re → t1_poleRemovedZeta s ≠ 0 := by
  obtain ⟨c,T,hc,hT,hz⟩ := h
  obtain ⟨ε,hε,hsmall⟩ := t1_poleRemovedZeta_compact_height T
  let b := min c (min ε (1/4))
  have hb : 0 < b := lt_min hc (lt_min hε (by norm_num))
  have hbε : b ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hbc : b ≤ c := min_le_left _ _
  refine ⟨b,hb,(min_le_right _ _).trans (min_le_right _ _),?_⟩
  intro s hs
  by_cases ht : T ≤ |s.im|
  · have hw : t1_vkHeightWidth b s.im ≤ t1_vkHeightWidth c s.im :=
      div_le_div_of_nonneg_right hbc (zero_le_one.trans (t1_vkHeightDenom_ge_one s.im))
    have hn : s ≠ 1 := by rintro rfl; simp at ht; linarith
    simpa only [t1_poleRemovedZeta,Function.update_of_ne hn] using
      mul_ne_zero (sub_ne_zero.mpr hn) (hz s ht (by linarith))
  · have hw := (t1_vkHeightWidth_le hb.le s.im).trans hbε
    exact hsmall s (le_of_lt (not_le.mp ht)) (by linarith)

end Markov
