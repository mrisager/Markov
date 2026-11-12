import T1BlaschkeFactor
import T1AnalyticDiskZeros
import Mathlib.Analysis.Complex.AbsMax

/-! Finite canonical decomposition on a zero-free boundary, with the
actual divisor and exact preservation of the boundary norm. -/

namespace Markov
open Complex Metric Set
open scoped ComplexConjugate
noncomputable section

private theorem analyticAt_prod {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ) (z : ℂ)
    (h : ∀ a ∈ S, AnalyticAt ℂ (F a) z) :
    AnalyticAt ℂ (fun w => ∏ a ∈ S, F a w) z := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (analyticAt_const (𝕜 := ℂ) (v := (1 : ℂ)) (x := z))
  | insert a S ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a S)).mul
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

private theorem blaschke_times_correction {r : ℝ} (hr : 0 < r) {a z : ℂ}
    (ha : ‖a‖ < r) (hz : ‖z‖ ≤ r) :
    t1_blaschkeFactor r a z * (t1_blaschkeDenom r a z / (r : ℂ)) = z-a := by
  have hd := t1_blaschkeDenom_ne_zero hr ha hz
  have hn : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold t1_blaschkeFactor
  field_simp

theorem t1_analytic_disk_canonical_product {f : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (h0 : f 0 ≠ 0)
    (hb : ∀ z : ℂ, ‖z‖ = r → f z ≠ 0) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ a : ℂ, a ∈ S ↔ a ∈ closedBall 0 r ∧ f a = 0) ∧
      (∀ a ∈ S, 0 < m a ∧ ‖a‖ < r ∧ a ≠ 0) ∧
      AnalyticOnNhd ℂ g (closedBall 0 r) ∧
      (∀ z ∈ closedBall 0 r, g z ≠ 0) ∧
      EqOn f (fun z => (∏ a ∈ S, t1_blaschkeFactor r a z ^ m a) * g z)
        (closedBall 0 r) ∧
      (∀ z : ℂ, ‖z‖ = r → ‖g z‖ = ‖f z‖) ∧
      ‖f 0‖ ≤ ‖g 0‖ := by
  obtain ⟨S,m,F,hS,hm,hF,hFn,hE⟩ := t1_analytic_disk_finite_zero_factorization hr hf h0 hb
  let C (a z : ℂ) := t1_blaschkeDenom r a z / (r : ℂ)
  let g (z : ℂ) := (∏ a ∈ S, C a z ^ m a) * F z
  have hn : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hg : AnalyticOnNhd ℂ g (closedBall 0 r) := by
    intro z hz
    apply AnalyticAt.mul ?_ (hF z hz)
    apply analyticAt_prod S
    intro a _
    apply AnalyticAt.pow
    dsimp only [C,t1_blaschkeDenom]
    exact (by fun_prop : AnalyticAt ℂ
      (fun z : ℂ => (r : ℂ)^2 - conj a * z) z).div analyticAt_const hn
  have hgn (z : ℂ) (hz : z ∈ closedBall 0 r) : g z ≠ 0 := by
    apply mul_ne_zero ?_ (hFn z hz)
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    have hz' : ‖z‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hz
    exact pow_ne_zero _ (div_ne_zero (t1_blaschkeDenom_ne_zero hr (hm a ha).2.1 hz') hn)
  have he : EqOn f (fun z => (∏ a ∈ S, t1_blaschkeFactor r a z ^ m a) * g z)
      (closedBall 0 r) := by
    intro z hz
    have hz' : ‖z‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hz
    rw [hE hz]
    dsimp only [g]
    rw [← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro a ha
    rw [← mul_pow, blaschke_times_correction hr (hm a ha).2.1 hz']
  refine ⟨S,m,g,hS,hm,hg,hgn,he,?_,?_⟩
  · intro z hz
    have hz' : z ∈ closedBall 0 r := by simp [mem_closedBall,dist_zero_right,hz]
    have hB : ‖∏ a ∈ S, t1_blaschkeFactor r a z ^ m a‖ = 1 := by
      rw [norm_prod]
      apply Finset.prod_eq_one
      intro a ha
      rw [norm_pow,t1_norm_blaschkeFactor_boundary hr (hm a ha).2.1 hz,one_pow]
    calc
      ‖g z‖ = 1 * ‖g z‖ := (one_mul _).symm
      _ = ‖∏ a ∈ S, t1_blaschkeFactor r a z ^ m a‖ * ‖g z‖ := by rw [hB]
      _ = ‖(∏ a ∈ S, t1_blaschkeFactor r a z ^ m a) * g z‖ := (norm_mul _ _).symm
      _ = ‖f z‖ := congrArg norm (he hz').symm
  · rw [he (mem_closedBall_self hr.le),norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [norm_prod]
    apply Finset.prod_le_one (fun a _ => norm_nonneg _)
    intro a ha
    rw [norm_pow,t1_norm_blaschkeFactor_zero hr]
    exact pow_le_one₀ (by positivity) ((div_le_one hr).mpr (hm a ha).2.1.le)

theorem t1_disk_residual_bound {f g : ℂ → ℂ} {r B : ℝ} (hr : 0 < r)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r))
    (hb : ∀ z : ℂ, ‖z‖ = r → ‖g z‖ = ‖f z‖)
    (hB : ∀ z ∈ closedBall (0 : ℂ) r, ‖f z‖ ≤ B) :
    ∀ z ∈ closedBall (0 : ℂ) r, ‖g z‖ ≤ B := by
  intro z hz
  have hd : DiffContOnCl ℂ g (ball 0 r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hr.ne']
    exact hg.differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd (z := z)
  · intro w hw
    rw [frontier_ball 0 hr.ne'] at hw
    have hn : ‖w‖ = r := by simpa only [mem_sphere,dist_zero_right] using hw
    rw [hb w hn]
    exact hB w (sphere_subset_closedBall hw)
  · rwa [closure_ball 0 hr.ne']

end
end Markov
