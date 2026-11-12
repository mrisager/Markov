import Markov.Statements
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.RemovableSingularity

/-! The actual reciprocal zeta function continued across the pole at one.
The half-plane holomorphy result uses exactly the paper's QRH hypothesis. -/
noncomputable section
open Filter ArithmeticFunction
open scoped Moebius
namespace Markov

def t1_poleRemovedZeta : ℂ → ℂ :=
  Function.update (fun s => (s-1)*riemannZeta s) 1 1

theorem t1_poleRemovedZeta_differentiable : Differentiable ℂ t1_poleRemovedZeta := by
  rw [← differentiableOn_univ,
    ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨DifferentiableOn.congr (f := fun s => (s-1)*riemannZeta s) ?_ ?_, ?_⟩
  · intro s hs
    have hn := (Set.mem_diff_singleton.mp hs).2
    exact ((differentiableAt_id.sub_const 1).mul
      (differentiableAt_riemannZeta hn)).differentiableWithinAt
  · intro s hs
    exact Function.update_of_ne (Set.mem_diff_singleton.mp hs).2 ..
  · simpa only [t1_poleRemovedZeta, continuousAt_update_same] using riemannZeta_residue_one

def t1_reciprocalZeta (s : ℂ) : ℂ := (s-1)/t1_poleRemovedZeta s

theorem t1_reciprocalZeta_one : t1_reciprocalZeta 1 = 0 := by
  simp [t1_reciprocalZeta]

theorem t1_reciprocalZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    t1_reciprocalZeta s = (riemannZeta s)⁻¹ := by
  simp only [t1_reciprocalZeta,t1_poleRemovedZeta,Function.update_of_ne hs]
  rw [div_mul_eq_div_div, div_self (sub_ne_zero.mpr hs), one_div]

theorem t1_poleRemovedZeta_ne_zero {δ : ℝ}
    (h : ∀ s : ℂ, s ≠ 1 → 1-δ < s.re → riemannZeta s ≠ 0)
    {s : ℂ} (hs : 1-δ < s.re) : t1_poleRemovedZeta s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hn
  · simp [t1_poleRemovedZeta]
  · simpa only [t1_poleRemovedZeta,Function.update_of_ne hn]
      using mul_ne_zero (sub_ne_zero.mpr hn) (h s hn hs)

theorem t1_reciprocalZeta_holomorphic_of_QRH (h : QuasiRiemannHypothesis) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧
      DifferentiableOn ℂ t1_reciprocalZeta {s : ℂ | 1-δ < s.re} := by
  obtain ⟨δ,hδ,hz⟩ := h
  let ε := min δ (1/4)
  have hεδ : ε ≤ δ := min_le_left _ _
  refine ⟨ε,lt_min hδ (by norm_num),min_le_right _ _,?_⟩
  intro s hs
  have hs' : 1-δ < s.re := (sub_le_sub_left hεδ 1).trans_lt hs
  exact ((differentiableAt_id.sub_const 1).div
    (t1_poleRemovedZeta_differentiable s)
    (t1_poleRemovedZeta_ne_zero hz hs')).differentiableWithinAt

theorem t1_reciprocalZeta_eq_moebius_LSeries {s : ℂ} (hs : 1 < s.re) :
    t1_reciprocalZeta s = LSeries (fun n => (μ n : ℂ)) s := by
  have hn : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [t1_reciprocalZeta_of_ne_one hn]
  have h := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at h
  exact (eq_inv_of_mul_eq_one_right h).symm

end Markov
