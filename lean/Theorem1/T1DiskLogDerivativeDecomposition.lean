import T1DiskCanonicalProduct
import T1DiskLogDerivBound

/-! The complete signed logarithmic derivative keeps every zero, with
its positive natural multiplicity and the exact radial correction. -/

namespace Markov
open Complex Filter Metric Set
open scoped ComplexConjugate Topology
noncomputable section

def t1_blaschkeLogTerm (r : ℝ) (a : ℂ) : ℂ :=
  -1/a + conj a / (r : ℂ)^2

theorem t1_blaschkeLogTerm_re {r : ℝ} (hr : 0 < r) {a : ℂ} (ha : a ≠ 0) :
    (t1_blaschkeLogTerm r a).re = -a.re * (1/‖a‖^2 - 1/r^2) := by
  have h := (norm_pos_iff.mpr ha).ne'
  unfold t1_blaschkeLogTerm
  simp only [← Complex.ofReal_pow,Complex.add_re,Complex.div_re,
    Complex.neg_re,Complex.neg_im,Complex.one_re,Complex.one_im,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.normSq_eq_norm_sq,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg r)]
  field_simp
  ring

theorem t1_blaschkeLogTerm_re_nonneg {r : ℝ} (hr : 0 < r) {a : ℂ}
    (ha : a ≠ 0) (har : ‖a‖ < r) (hre : a.re ≤ 0) :
    0 ≤ (t1_blaschkeLogTerm r a).re := by
  rw [t1_blaschkeLogTerm_re hr ha]
  apply mul_nonneg (neg_nonneg.mpr hre) (sub_nonneg.mpr _)
  apply one_div_le_one_div_of_le (by positivity)
  exact (sq_le_sq₀ (norm_nonneg _) hr.le).mpr har.le

theorem t1_logDeriv_of_disk_canonical_product {f g : ℂ → ℂ} {r : ℝ}
    {S : Finset ℂ} {m : ℂ → ℕ} (hr : 0 < r)
    (hm : ∀ a ∈ S, ‖a‖ < r ∧ a ≠ 0)
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 ≠ 0)
    (he : EqOn f (fun z => (∏ a ∈ S, t1_blaschkeFactor r a z ^ m a) * g z)
      (closedBall 0 r)) :
    logDeriv f 0 = logDeriv g 0 + ∑ a ∈ S, (m a : ℂ) * t1_blaschkeLogTerm r a := by
  have hN : closedBall (0 : ℂ) r ∈ 𝓝 0 := closedBall_mem_nhds _ hr
  have hEq := he.eventuallyEq_of_mem hN
  let B (z : ℂ) := ∏ a ∈ S, t1_blaschkeFactor r a z ^ m a
  have h0 (a : ℂ) (ha : a ∈ S) : t1_blaschkeFactor r a 0 ^ m a ≠ 0 :=
    pow_ne_zero _ (t1_blaschkeFactor_ne_zero hr (hm a ha).1 (by simp [hr.le]) (hm a ha).2.symm)
  have hD (a : ℂ) (ha : a ∈ S) : DifferentiableAt ℂ (t1_blaschkeFactor r a) 0 :=
    (t1_blaschkeFactor_analyticAt hr (hm a ha).1 (by simp [hr.le])).differentiableAt
  have hB0 : B 0 ≠ 0 := Finset.prod_ne_zero_iff.mpr h0
  have hBd : DifferentiableAt ℂ B 0 :=
    .fun_finset_prod (fun a ha => (hD a ha).pow (m a))
  calc
    _ = logDeriv (fun z => B z * g z) 0 := by
      rw [logDeriv_apply,logDeriv_apply,hEq.deriv_eq,hEq.eq_of_nhds]
    _ = _ := by
      rw [logDeriv_mul 0 hB0 hg0 hBd hg.differentiableAt,add_comm]
      congr 1
      unfold B
      have hsum := logDeriv_prod (f := fun a z => t1_blaschkeFactor r a z ^ m a)
        h0 (fun a ha => (hD a ha).pow (m a))
      rw [hsum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [logDeriv_fun_pow (hD a ha), t1_logDeriv_blaschkeFactor_zero hr (hm a ha).1 (hm a ha).2]
      rfl

theorem t1_disk_logDeriv_decomposition {f : ℂ → ℂ} {R B C : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    (hA : 0 < B+C) (hB : ∀ z ∈ closedBall (0 : ℂ) R, ‖f z‖ ≤ Real.exp B)
    (hC : -Real.log ‖f 0‖ ≤ C) :
    ∃ (r : ℝ) (S : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      R/2 < r ∧ r < 3*R/4 ∧
      (∀ a : ℂ, a ∈ S ↔ a ∈ closedBall 0 r ∧ f a = 0) ∧
      (∀ a ∈ S, 0 < m a ∧ ‖a‖ < r ∧ a ≠ 0) ∧
      ‖logDeriv g 0‖ ≤ 4*(B+C)/R ∧
      logDeriv f 0 = logDeriv g 0 + ∑ a ∈ S, (m a : ℂ) * t1_blaschkeLogTerm r a := by
  obtain ⟨r,hrlo,hrhi,hb⟩ := t1_analytic_disk_exists_zeroFree_sphere hR hf h0
  have hr : 0 < r := by linarith
  have hsub : closedBall (0 : ℂ) r ⊆ closedBall 0 R :=
    closedBall_subset_closedBall (by linarith)
  obtain ⟨S,m,g,hS,hm,hg,hgn,he,hnorm,hcenter⟩ :=
    t1_analytic_disk_canonical_product hr (hf.mono hsub) h0 hb
  have hBg := t1_disk_residual_bound hr hg hnorm (fun z hz => hB z (hsub hz))
  have hCg : -Real.log ‖g 0‖ ≤ C :=
    (neg_le_neg (Real.log_le_log (norm_pos_iff.mpr h0) hcenter)).trans hC
  have hd := t1_disk_norm_logDeriv_center_le hr hg hgn hA hBg hCg
  have hu := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2*(B+C))
    (by positivity : 0 < R/2) hrlo.le
  have hG : ‖logDeriv g 0‖ ≤ 4*(B+C)/R :=
    hd.trans (hu.trans_eq (by ring))
  refine ⟨r,S,m,g,hrlo,hrhi,hS,hm,hG,?_⟩
  exact t1_logDeriv_of_disk_canonical_product hr (fun a ha => (hm a ha).2)
    (hg 0 (mem_closedBall_self hr.le)) (hgn 0 (mem_closedBall_self hr.le)) he

end
end Markov
