import Markov.FiniteLatticeReciprocalSquare
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! A quantitative fourth-power tail on the full standard integer lattice.
The proof integrates the finite counting function and then passes to a
genuinely summable nonnegative series. -/

noncomputable section
open Set MeasureTheory
namespace Markov

/-- The inverse fourth power is the tail integral of its positive power kernel. -/
theorem inv_fourth_eq_four_integral_Ioi_rpow_neg_five (x : ℝ) (hx : 0 < x) :
    1 / x ^ (4 : ℕ) = 4 * ∫ t : ℝ in Ioi x, t ^ (-5 : ℝ) := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-5 : ℝ) < -1) hx]
  norm_num
  field_simp

/-- A finite family with a quadratic initial-segment bound has a
fourth-power tail bounded by `2 C / K²`. -/
theorem finite_sum_reciprocal_fourth_le_of_quadratic_count
    {ι : Type*} (S : Finset ι) (r : ι → ℝ) (C K : ℝ) (hK : 0 < K)
    (hr : ∀ i ∈ S, K ≤ r i)
    (hcount : ∀ T : ℝ, K ≤ T →
      ((S.filter fun i => r i ≤ T).card : ℝ) ≤ C * T ^ (2 : ℕ)) :
    (∑ i ∈ S, 1 / r i ^ (4 : ℕ)) ≤ 2 * C / K ^ (2 : ℕ) := by
  classical
  let k : ι → ℝ → ℝ := fun i => (Ioi (r i)).indicator (fun t : ℝ => t ^ (-5 : ℝ))
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-5 : ℝ)) (Ioi K) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hK
  have hk (i : ι) : IntegrableOn (k i) (Ioi K) := hbase.indicator measurableSet_Ioi
  have hmajor : IntegrableOn (fun t : ℝ => C * t ^ (-3 : ℝ)) (Ioi K) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hK).const_mul C
  have hpoint (t : ℝ) (ht : t ∈ Ioi K) : ∑ i ∈ S, k i t ≤ C * t ^ (-3 : ℝ) := by
    have htpos : 0 < t := hK.trans ht
    have hcard : ((S.filter fun i => r i < t).card : ℝ) ≤ C * t ^ (2 : ℕ) := by
      refine le_trans ?_ (hcount t ht.le)
      exact_mod_cast Finset.card_le_card (show (S.filter fun i => r i < t) ⊆
        (S.filter fun i => r i ≤ t) from fun i hi => by
          simp only [Finset.mem_filter] at hi ⊢
          exact ⟨hi.1, hi.2.le⟩)
    have heq : ∑ i ∈ S, k i t =
        ((S.filter fun i => r i < t).card : ℝ) * t ^ (-5 : ℝ) := by
      simp [k, Set.indicator_apply, ← Finset.sum_filter]
    rw [heq]
    calc
      _ ≤ (C * t ^ (2 : ℕ)) * t ^ (-5 : ℝ) :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg htpos.le _)
      _ = C * t ^ (-3 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add htpos]
        norm_num
  have hint := setIntegral_mono_on (integrable_finset_sum S (fun i _ => hk i)) hmajor
    measurableSet_Ioi hpoint
  have hidentity : (∑ i ∈ S, 1 / r i ^ (4 : ℕ)) =
      4 * ∫ t : ℝ in Ioi K, ∑ i ∈ S, k i t := by
    rw [integral_finset_sum S (fun i _ => hk i), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inv_fourth_eq_four_integral_Ioi_rpow_neg_five (r i) (hK.trans_le (hr i hi))]
    congr 1
    rw [show k i = (Ioi (r i)).indicator (fun t : ℝ => t ^ (-5 : ℝ)) by rfl,
      setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (hr i hi))]
  have heval : (∫ t : ℝ in Ioi K, C * t ^ (-3 : ℝ)) = C / (2 * K ^ (2 : ℕ)) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hK]
    norm_num
    field_simp
  rw [hidentity]
  have hbound := mul_le_mul_of_nonneg_left hint (by norm_num : (0 : ℝ) ≤ 4)
  rw [heval] at hbound
  convert hbound using 1
  field_simp
  ring

/-- The actual finite full-lattice tail has an explicit uniform `K⁻²` bound. -/
theorem finite_integer_fourth_power_tail_le (S : Finset (ℤ × ℤ))
    (K : ℝ) (hK : 1 ≤ K) :
    (∑ d ∈ S, if K < intEuclidean d then 1 / intEuclidean d ^ (4 : ℕ) else 0) ≤
      50 / K ^ (2 : ℕ) := by
  classical
  rw [← Finset.sum_filter]
  have hbound := finite_sum_reciprocal_fourth_le_of_quadratic_count
    (S.filter fun d => K < intEuclidean d) intEuclidean 25 K (by linarith)
    (fun d hd => (Finset.mem_filter.mp hd).2.le)
    (fun T hT => finite_integer_direction_count_le_quadratic _ T (hK.trans hT))
  norm_num at hbound
  simpa only [one_div] using hbound

/-- The full fourth-power tail is genuinely summable. -/
theorem integer_fourth_power_tail_summable (K : ℝ) (hK : 1 ≤ K) :
    Summable (fun d : ℤ × ℤ =>
      if K < intEuclidean d then 1 / intEuclidean d ^ (4 : ℕ) else 0) := by
  apply summable_of_sum_le
  · intro d
    change 0 ≤ (if K < intEuclidean d then 1 / intEuclidean d ^ (4 : ℕ) else 0)
    split_ifs <;> positivity
  · intro S
    exact finite_integer_fourth_power_tail_le S K hK

/-- Quantitative full-lattice fourth-power tail, including its explicit constant. -/
theorem integer_fourth_power_tail_le (K : ℝ) (hK : 1 ≤ K) :
    (∑' d : ℤ × ℤ, if K < intEuclidean d then
      1 / intEuclidean d ^ (4 : ℕ) else 0) ≤ 50 / K ^ (2 : ℕ) := by
  apply Real.tsum_le_of_sum_le
  · intro d
    change 0 ≤ (if K < intEuclidean d then 1 / intEuclidean d ^ (4 : ℕ) else 0)
    split_ifs <;> positivity
  · intro S
    exact finite_integer_fourth_power_tail_le S K hK

end Markov
