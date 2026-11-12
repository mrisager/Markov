import T1ZetaDiskLogDerivative

/-! Signed bounds for the local logarithmic derivative of the actual
zeta function, with and without a selected zero at the same height. -/

namespace Markov
open Complex Filter Metric Set
open scoped ComplexConjugate Topology
noncomputable section

def t1_zetaRadiusBudget (B x R : ℝ) : ℝ :=
  4*(B+Real.log (2+1/x))/R

private theorem sum_re_eq {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    (∑ a ∈ S, f a).re = ∑ a ∈ S, (f a).re := by
  exact map_sum Complex.reCLM f S

theorem t1_neg_logDeriv_zeta_disc_le {R B x t : ℝ}
    (hR : 0 < R) (hRu : R ≤ 1) (hB : 0 ≤ B) (hx : 0 < x) (ht : 2 ≤ |t|)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) R, ‖t1_zetaDiscTranslate x t z‖ ≤ Real.exp B) :
    (-logDeriv riemannZeta (t1_verticalPoint (1+x) t)).re ≤ t1_zetaRadiusBudget B x R := by
  obtain ⟨r,S,m,v,_,_,_,hm,hv,he⟩ := t1_zetaDiscLogDerivative_split hR hRu hB hx ht hbound
  have hn : 0 ≤ ∑ a ∈ S, ((m a : ℂ)*t1_blaschkeLogTerm r a).re :=
    Finset.sum_nonneg (fun a ha => (hm a ha).2.2.2)
  have hvr : -v.re ≤ ‖v‖ := by simpa only [Complex.neg_re,norm_neg] using Complex.re_le_norm (-v)
  rw [he,Complex.neg_re,Complex.add_re,sum_re_eq]
  unfold t1_zetaRadiusBudget
  linarith

theorem t1_neg_logDeriv_zeta_disc_le_sub_zero {R B x : ℝ} {ρ : ℂ}
    (hR : 0 < R) (hRu : R ≤ 1) (hB : 0 ≤ B) (hx : 0 < x) (ht : 2 ≤ |ρ.im|)
    (hzero : riemannZeta ρ = 0) (hnear : x+1-ρ.re < R/2)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) R,
      ‖t1_zetaDiscTranslate x ρ.im z‖ ≤ Real.exp B) :
    (-logDeriv riemannZeta (t1_verticalPoint (1+x) ρ.im)).re ≤
      t1_zetaRadiusBudget B x R - (1/(x+1-ρ.re) - 4*(x+1-ρ.re)/R^2) := by
  classical
  let d : ℝ := x+1-ρ.re
  let a := ρ - t1_verticalPoint (1+x) ρ.im
  have hρ : ρ.re < 1 := by
    by_contra! hn
    exact riemannZeta_ne_zero_of_one_le_re hn hzero
  have hd : 0 < d := by dsimp [d]; linarith
  have ha : a = ((-d : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [a,d,t1_verticalPoint_re]
      ring
    · simp [a,t1_verticalPoint_im]
  have haNorm : ‖a‖ = d := by
    rw [ha,Complex.norm_real,Real.norm_eq_abs,abs_neg,abs_of_pos hd]
  have hza : t1_zetaDiscTranslate x ρ.im a = 0 := by
    simp [t1_zetaDiscTranslate,a,hzero]
  obtain ⟨r,S,m,v,hrlo,hrhi,hS,hm,hv,he⟩ :=
    t1_zetaDiscLogDerivative_split hR hRu hB hx ht hbound
  have hr : 0 < r := by linarith
  have hda : d < r := hnear.trans hrlo
  have haS : a ∈ S := (hS a).mpr
    ⟨by simp only [mem_closedBall,dist_zero_right,haNorm]; exact hda.le,hza⟩
  have ha0 := (hm a haS).2.2.1
  have hk : (t1_blaschkeLogTerm r a).re = 1/d - d/r^2 := by
    rw [t1_blaschkeLogTerm_re hr ha0,haNorm,ha,Complex.ofReal_re,neg_neg]
    field_simp
  have h0 := t1_blaschkeLogTerm_re_nonneg hr ha0 (by rwa [haNorm]) (by rw [ha,Complex.ofReal_re]; linarith)
  have hm1 : (1 : ℝ) ≤ (m a : ℝ) := by exact_mod_cast (hm a haS).1
  have hml := mul_le_mul_of_nonneg_right hm1 h0
  have hRe : ((m a : ℂ)*t1_blaschkeLogTerm r a).re =
      (m a : ℝ)*(t1_blaschkeLogTerm r a).re := by
    rw [show (m a : ℂ) = ((m a : ℝ) : ℂ) by exact_mod_cast rfl,Complex.re_ofReal_mul]
  rw [one_mul, ← hRe, hk] at hml
  have hsum : ((m a : ℂ)*t1_blaschkeLogTerm r a).re ≤
      ∑ b ∈ S, ((m b : ℂ)*t1_blaschkeLogTerm r b).re :=
    Finset.single_le_sum (fun b hb => (hm b hb).2.2.2) haS
  have hc : d/r^2 ≤ 4*d/R^2 := by
    have h := div_le_div_of_nonneg_left hd.le (by positivity : 0 < (R/2)^2)
      ((sq_le_sq₀ (by positivity) hr.le).mpr hrlo.le)
    exact h.trans_eq (by ring)
  have hvr : -v.re ≤ ‖v‖ := by simpa only [Complex.neg_re,norm_neg] using Complex.re_le_norm (-v)
  change _ ≤ t1_zetaRadiusBudget B x R - (1/d - 4*d/R^2)
  rw [he,Complex.neg_re,Complex.add_re,sum_re_eq]
  unfold t1_zetaRadiusBudget
  linarith

end
end Markov
