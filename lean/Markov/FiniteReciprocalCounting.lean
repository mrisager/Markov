import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Finite inverse-length partial summation. A quadratic counting bound on a
finite annulus gives a reciprocal-length bound with no logarithmic loss. -/

noncomputable section
open Set MeasureTheory

namespace Markov

theorem inv_eq_integral_Ioi_rpow_neg_two (x : ℝ) (hx : 0 < x) :
    1 / x = ∫ t : ℝ in Ioi x, t ^ (-2 : ℝ) := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx]
  norm_num [Real.rpow_neg_one]

/-- The finite-annulus form of inverse-length partial summation used in
Corollary 11. The counting hypothesis is needed only between `L` and `K`. -/
theorem finite_sum_inv_le_of_count_quadratic
    {ι : Type*} (S : Finset ι) (r : ι → ℝ) (C α L K : ℝ)
    (hL : 0 < L) (hLK : L ≤ K) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hr : ∀ i ∈ S, L ≤ r i ∧ r i ≤ K)
    (hcount : ∀ T : ℝ, L ≤ T → T ≤ K →
      ((S.filter fun i => r i ≤ T).card : ℝ) ≤ C * (1 + α * T ^ 2)) :
    ∑ i ∈ S, 1 / r i ≤ C / L + 2 * C * α * K := by
  classical
  let p : ℝ → ℝ := fun t => t ^ (-2 : ℝ)
  let k : ι → ℝ → ℝ := fun i => (Ioi (r i)).indicator p
  let b : ℝ → ℝ := (Ioc L K).indicator (fun _ => C * α)
  let c : ℝ → ℝ := (Ioi K).indicator (fun t => C * α * K ^ 2 * p t)
  have hK : 0 < K := hL.trans_le hLK
  have hp : IntegrableOn p (Ioi L) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hL
  have hk (i : ι) : IntegrableOn (k i) (Ioi L) :=
    hp.indicator measurableSet_Ioi
  have hbglobal : Integrable b := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    exact integrableOn_const (by simp)
  have hb : IntegrableOn b (Ioi L) := hbglobal.integrableOn
  have hc : IntegrableOn c (Ioi L) :=
    (hp.const_mul (C * α * K ^ 2)).indicator measurableSet_Ioi
  have hmajor : IntegrableOn (fun t => C * p t + b t + c t) (Ioi L) :=
    ((hp.const_mul C).add hb).add hc
  have hpoint (t : ℝ) (ht : t ∈ Ioi L) :
      ∑ i ∈ S, k i t ≤ C * p t + b t + c t := by
    have htpos : 0 < t := hL.trans ht
    have hpnonneg : 0 ≤ p t := Real.rpow_nonneg htpos.le _
    have htp : t ^ 2 * p t = 1 := by
      dsimp [p]
      rw [Real.rpow_neg htpos.le, Real.rpow_two]
      exact mul_inv_cancel₀ (pow_ne_zero 2 htpos.ne')
    have heq : ∑ i ∈ S, k i t =
        ((S.filter fun i => r i < t).card : ℝ) * p t := by
      simp [k, Set.indicator_apply, ← Finset.sum_filter]
    rw [heq]
    by_cases htK : t ≤ K
    · have hcard : ((S.filter fun i => r i < t).card : ℝ) ≤
          C * (1 + α * t ^ 2) := by
        refine le_trans ?_ (hcount t ht.le htK)
        exact_mod_cast Finset.card_le_card (show
          (S.filter fun i => r i < t) ⊆ (S.filter fun i => r i ≤ t) from
          fun i hi => by simp only [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.le⟩)
      have hm := mul_le_mul_of_nonneg_right hcard hpnonneg
      have heval : C * (1 + α * t ^ 2) * p t = C * p t + C * α := by
        calc
          _ = C * p t + C * α * (t ^ 2 * p t) := by ring
          _ = _ := by rw [htp]; ring
      rw [heval] at hm
      simpa [b, c, Set.indicator_of_mem (show t ∈ Ioc L K from ⟨ht, htK⟩),
        not_lt.mpr htK] using hm
    · have hcard : ((S.filter fun i => r i < t).card : ℝ) ≤
          C * (1 + α * K ^ 2) := by
        have hall : S.filter (fun i => r i ≤ K) = S :=
          Finset.filter_eq_self.mpr (fun i hi => (hr i hi).2)
        calc
          _ ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_filter_le S _
          _ ≤ _ := by simpa [hall] using hcount K hLK le_rfl
      have hm := mul_le_mul_of_nonneg_right hcard hpnonneg
      simpa [b, c, htK, lt_of_not_ge htK, mul_add, add_mul, mul_assoc] using hm
  have hint := setIntegral_mono_on
    (integrable_finset_sum S (fun i _ => hk i)) hmajor measurableSet_Ioi hpoint
  have hidentity : ∑ i ∈ S, 1 / r i =
      ∫ t : ℝ in Ioi L, ∑ i ∈ S, k i t := by
    rw [integral_finset_sum S (fun i _ => hk i)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inv_eq_integral_Ioi_rpow_neg_two (r i) (hL.trans_le (hr i hi).1)]
    rw [show k i = (Ioi (r i)).indicator p by rfl,
      setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (hr i hi).1)]
  have hbval : (∫ t : ℝ in Ioi L, b t) = C * α * (K - L) := by
    rw [show b = (Ioc L K).indicator (fun _ => C * α) by rfl,
      setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr Ioc_subset_Ioi_self]
    simp [integral_const, max_eq_left (sub_nonneg.mpr hLK)]
    ring
  have hcval : (∫ t : ℝ in Ioi L, c t) = C * α * K := by
    rw [show c = (Ioi K).indicator (fun t => C * α * K ^ 2 * p t) by rfl,
      setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi hLK), integral_const_mul,
      ← inv_eq_integral_Ioi_rpow_neg_two K hK]
    field_simp
  have hmain : (∫ t : ℝ in Ioi L, C * p t + b t + c t) =
      C / L + C * α * (K - L) + C * α * K := by
    rw [integral_add (f := fun t => C * p t + b t) (g := c)
        ((hp.const_mul C).add hb) hc,
      integral_add (f := fun t => C * p t) (g := b) (hp.const_mul C) hb, integral_const_mul,
      ← inv_eq_integral_Ioi_rpow_neg_two L hL, hbval, hcval]
    ring
  rw [← hidentity, hmain] at hint
  have hnonneg : 0 ≤ C * α * L := mul_nonneg (mul_nonneg hC hα) hL.le
  nlinarith

end Markov
