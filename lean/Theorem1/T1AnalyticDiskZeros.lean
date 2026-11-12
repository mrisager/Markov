import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-! A genuine finite zero factorization on the entire closed disk.
The finite support and multiplicities are the actual analytic divisor. -/

namespace Markov
open Complex Filter Function MeromorphicOn Metric Set Topology
noncomputable section

private theorem order_ne_top {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (h0 : f 0 ≠ 0) :
    ∀ z : closedBall (0 : ℂ) r, meromorphicOrderAt f z ≠ ⊤ := by
  have hz : (0 : ℂ) ∈ closedBall 0 r := mem_closedBall_self hr.le
  have ho := (hf 0 hz).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0
  exact (hf.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
    (Metric.isConnected_closedBall hr.le)).mp ⟨⟨0,hz⟩, by simp [ho]⟩

theorem t1_analytic_disk_exists_zeroFree_sphere {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (h0 : f 0 ≠ 0) :
    ∃ s : ℝ, r/2 < s ∧ s < 3*r/4 ∧ ∀ z : ℂ, ‖z‖ = s → f z ≠ 0 := by
  classical
  have hzeros : (closedBall 0 r ∩ f ⁻¹' {0}).Finite := by
    rw [hf.meromorphicNFOn.zero_set_eq_divisor_support (order_ne_top hr hf h0)]
    exact (divisor f (closedBall 0 r)).finiteSupport (isCompact_closedBall 0 r)
  let bad : Finset ℝ := hzeros.toFinset.image norm
  have hnot : ¬ Ioo (r/2) (3*r/4) ⊆ (bad : Set ℝ) := by
    intro h
    exact (Set.Ioo_infinite (by linarith : r/2 < 3*r/4)) (bad.finite_toSet.subset h)
  obtain ⟨s, hs, hbad⟩ := Set.not_subset.mp hnot
  refine ⟨s, hs.1, hs.2, fun z hz hz0 => hbad ?_⟩
  apply Finset.mem_coe.mpr
  apply Finset.mem_image.mpr
  refine ⟨z, ?_, hz⟩
  rw [Set.Finite.mem_toFinset]
  refine ⟨?_, hz0⟩
  rw [mem_closedBall, dist_zero_right, hz]
  linarith [hs.2]

private theorem eqOn_of_disk_codiscrete {f g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (closedBall 0 r)) (hg : ContinuousOn g (closedBall 0 r))
    (he : f =ᶠ[codiscreteWithin (closedBall 0 r)] g) :
    EqOn f g (closedBall 0 r) := by
  have hin : EqOn f g (ball 0 r) := by
    intro z hz
    have h := he.filter_mono (show 𝓝[closedBall (0 : ℂ) r \ {z}] z ≤
        codiscreteWithin (closedBall 0 r) from
      le_iSup_of_le z (le_iSup_of_le (ball_subset_closedBall hz) le_rfl))
    have hnb : closedBall (0 : ℂ) r ∈ 𝓝 z :=
      Filter.mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall
    rw [Set.diff_eq, nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hnb)] at h
    have hfc := hf.continuousAt hnb
    have hgc := hg.continuousAt hnb
    exact ((hfc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hgc).1 h).eq_of_nhds
  apply hin.of_subset_closure hf hg ball_subset_closedBall
  rw [closure_ball 0 hr.ne']

/-- Zeros in a disk with zero-free boundary give a finite product, with
positive natural multiplicities and a holomorphic nowhere-zero residual. -/
theorem t1_analytic_disk_finite_zero_factorization {f : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (h0 : f 0 ≠ 0)
    (hb : ∀ z : ℂ, ‖z‖ = r → f z ≠ 0) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ a : ℂ, a ∈ S ↔ a ∈ closedBall 0 r ∧ f a = 0) ∧
      (∀ a ∈ S, 0 < m a ∧ ‖a‖ < r ∧ a ≠ 0) ∧
      AnalyticOnNhd ℂ g (closedBall 0 r) ∧
      (∀ z ∈ closedBall 0 r, g z ≠ 0) ∧
      EqOn f (fun z => (∏ a ∈ S, (z-a)^m a) * g z) (closedBall 0 r) := by
  classical
  let D := divisor f (closedBall 0 r)
  have hD : D.support.Finite := D.finiteSupport (isCompact_closedBall 0 r)
  let S := hD.toFinset
  let m (a : ℂ) : ℕ := (D a).toNat
  have hS (a : ℂ) : a ∈ S ↔ a ∈ closedBall 0 r ∧ f a = 0 := by
    unfold S
    rw [Set.Finite.mem_toFinset]
    change a ∈ Function.support (divisor f (closedBall 0 r)) ↔ _
    rw [← hf.meromorphicNFOn.zero_set_eq_divisor_support (order_ne_top hr hf h0)]
    rfl
  have hm (a : ℂ) : (m a : ℤ) = D a :=
    Int.toNat_of_nonneg (hf.divisor_nonneg a)
  have hm' (a : ℂ) (ha : a ∈ S) : 0 < m a ∧ ‖a‖ < r ∧ a ≠ 0 := by
    have hn : D a ≠ 0 := by simpa only [S, Set.Finite.mem_toFinset, Function.mem_support] using ha
    have hmem := (hS a).mp ha
    have hnorm : ‖a‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hmem.1
    have hpos : 0 < m a := by have h := hm a; omega
    exact ⟨hpos, lt_of_le_of_ne hnorm (fun h => hb a h hmem.2),
      fun h => h0 (h ▸ hmem.2)⟩
  obtain ⟨g,hg,hgn,he⟩ := hf.meromorphicOn.extract_zeros_poles (order_ne_top hr hf h0) hD
  have hprod : (∏ᶠ a, (· - a) ^ D a) = fun z => ∏ a ∈ S, (z-a)^m a := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
    · ext z
      simp only [Finset.prod_apply]
      apply Finset.prod_congr rfl
      intro a _
      rw [← hm a, zpow_natCast]
      rfl
    · intro a ha
      by_contra hn
      have hda : D a = 0 := by
        by_contra hc
        apply hn
        change a ∈ hD.toFinset
        rw [Set.Finite.mem_toFinset]
        exact hc
      exact ha (by simp [hda])
  rw [hprod] at he
  refine ⟨S,m,g,hS,hm',hg,(fun z hz => hgn ⟨z,hz⟩), ?_⟩
  apply eqOn_of_disk_codiscrete hr hf.continuousOn ?_ he
  apply ContinuousOn.mul ?_ hg.continuousOn
  exact (continuous_finset_prod S (fun a _ =>
    (continuous_id.sub continuous_const).pow (m a))).continuousOn

end
end Markov
