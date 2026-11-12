import T1ReciprocalZetaStripBound

/-! The paper's QRH gives a genuine fixed strip with polynomially bounded
holomorphic reciprocal zeta, crossing the pole line at s=1. -/
noncomputable section
open Set
namespace Markov

theorem t1_QRH_reciprocalZeta_strip (h : QuasiRiemannHypothesis) :
    ∃ σ C A : ℝ, (1 : ℝ)/2 ≤ σ ∧ σ < 1 ∧ 0 < C ∧ 0 < A ∧
      DifferentiableOn ℂ t1_reciprocalZeta {s : ℂ | s.re ∈ Icc σ 2} ∧
      ∀ s : ℂ, s.re ∈ Icc σ 2 → ‖t1_reciprocalZeta s‖ ≤ C*(1+|s.im|)^A := by
  obtain ⟨δ,hδ,hz⟩ := h
  let ε := min δ (1/4)
  have hε : 0 < ε := lt_min hδ (by norm_num)
  have hε' : ε ≤ 1/4 := min_le_right _ _
  have hz' : ∀ s : ℂ, s ≠ 1 → 1-ε < s.re → riemannZeta s ≠ 0 := by
    intro s hn hs
    exact hz s hn ((sub_le_sub_left (min_le_left δ (1/4)) 1).trans_lt hs)
  obtain ⟨C,A,hC,hA,hbound⟩ := t1_reciprocalZeta_fixed_strip hε hε' hz'
  refine ⟨1-ε/2,C,A,by linarith,by linarith,hC,hA,?_,?_⟩
  · intro s hs
    have hh : 1-ε/2 ≤ s.re := hs.1
    exact ((differentiableAt_id.sub_const 1).div
      (t1_poleRemovedZeta_differentiable s)
      (t1_poleRemovedZeta_ne_zero hz' (by linarith : 1-ε < s.re))).differentiableWithinAt
  · exact fun s hs => hbound s hs.1 hs.2

end Markov
