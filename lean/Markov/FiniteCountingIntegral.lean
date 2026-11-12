import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! A uniform finite weighted-sum estimate from a quarter-power counting
bound. Integrating the finite counting function against `t^(-3/2)` is a
summation-by-parts identity; its majorant has integral `4 * C`. -/

noncomputable section
open Set MeasureTheory

namespace Markov

/-- The inverse square-root weight is the tail integral of its positive
power kernel. -/
theorem inv_sqrt_eq_half_integral_Ioi_rpow (x : ℝ) (hx : 0 < x) :
    1 / Real.sqrt x = (1 / 2 : ℝ) *
      ∫ t : ℝ in Ioi x, t ^ (-(3 / 2 : ℝ)) := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) hx]
  norm_num
  rw [show (-(1 / 2 : ℝ)) = -(1 / 2 : ℝ) by rfl, Real.rpow_neg hx.le,
    ← Real.sqrt_eq_rpow]
  ring

/-- If every initial segment of a finite set has cardinal at most
`C * T^(1/4)`, its inverse-square-root weights sum to at most `2 * C`.
The constant is uniform in the finite set and the radius function. -/
theorem finite_sum_inv_sqrt_le_of_count_quarter_rpow
    {ι : Type*} (S : Finset ι) (r : ι → ℝ) (C : ℝ)
    (hr : ∀ i ∈ S, 1 ≤ r i) (_hC : 0 ≤ C)
    (hcount : ∀ T : ℝ, 1 ≤ T →
      ((S.filter fun i => r i ≤ T).card : ℝ) ≤ C * T ^ (1 / 4 : ℝ)) :
    ∑ i ∈ S, 1 / Real.sqrt (r i) ≤ 2 * C := by
  classical
  let k : ι → ℝ → ℝ := fun i =>
    (Ioi (r i)).indicator (fun t : ℝ => t ^ (-(3 / 2 : ℝ)))
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hk (i : ι) : IntegrableOn (k i) (Ioi 1) :=
    hbase.indicator measurableSet_Ioi
  have hmajor : IntegrableOn (fun t : ℝ => C * t ^ (-(5 / 4 : ℝ))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(5 / 4 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul C
  have hpoint (t : ℝ) (ht : t ∈ Ioi (1 : ℝ)) :
      ∑ i ∈ S, k i t ≤ C * t ^ (-(5 / 4 : ℝ)) := by
    have htpos : 0 < t := lt_trans zero_lt_one ht
    have hcard : ((S.filter fun i => r i < t).card : ℝ) ≤ C * t ^ (1 / 4 : ℝ) := by
      refine le_trans ?_ (hcount t ht.le)
      exact_mod_cast Finset.card_le_card (show (S.filter fun i => r i < t) ⊆
        (S.filter fun i => r i ≤ t) from fun i hi => by
          simp only [Finset.mem_filter] at hi ⊢
          exact ⟨hi.1, hi.2.le⟩)
    have heq : ∑ i ∈ S, k i t =
        ((S.filter fun i => r i < t).card : ℝ) * t ^ (-(3 / 2 : ℝ)) := by
      simp [k, Set.indicator_apply, ← Finset.sum_filter]
    rw [heq]
    calc
      _ ≤ (C * t ^ (1 / 4 : ℝ)) * t ^ (-(3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg htpos.le _)
      _ = C * t ^ (-(5 / 4 : ℝ)) := by
        rw [mul_assoc, ← Real.rpow_add htpos]
        norm_num
  have hint : (∫ t : ℝ in Ioi 1, ∑ i ∈ S, k i t) ≤
      ∫ t : ℝ in Ioi 1, C * t ^ (-(5 / 4 : ℝ)) :=
    setIntegral_mono_on (integrable_finset_sum S (fun i _ => hk i)) hmajor
      measurableSet_Ioi hpoint
  have hidentity : ∑ i ∈ S, 1 / Real.sqrt (r i) =
      (1 / 2 : ℝ) * ∫ t : ℝ in Ioi 1, ∑ i ∈ S, k i t := by
    rw [integral_finset_sum S (fun i _ => hk i), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inv_sqrt_eq_half_integral_Ioi_rpow (r i) (by linarith [hr i hi])]
    congr 1
    rw [show k i = (Ioi (r i)).indicator
      (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) by rfl,
      setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (hr i hi))]
  have heval : (∫ t : ℝ in Ioi 1, C * t ^ (-(5 / 4 : ℝ))) = 4 * C := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt
      (by norm_num : -(5 / 4 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)]
    norm_num
    ring
  rw [hidentity]
  have hbound := mul_le_mul_of_nonneg_left hint (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [heval] at hbound
  nlinarith

end Markov
