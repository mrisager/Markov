import Markov.FareyScale
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! A logarithmic bound for the full nonzero lattice reciprocal-square sum.
The norm is the actual standard Euclidean integer-coordinate norm. -/

noncomputable section
open Set MeasureTheory

namespace Markov

private theorem integral_two_div_cube {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (2 : ℝ) / t ^ (3 : ℕ)) = 1 / a ^ (2 : ℕ) - 1 / b ^ (2 : ℕ) := by
  have hnot : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [uIcc_of_le hab]
    intro h
    exact (not_le_of_gt ha) h.1
  have hz := integral_zpow (a := a) (b := b) (n := (-3 : ℤ))
    (Or.inr ⟨by norm_num, hnot⟩)
  have hid : (fun t : ℝ ↦ (2 : ℝ) / t ^ (3 : ℕ)) = fun t ↦ 2 * t ^ (-3 : ℤ) := by
    funext t
    norm_num [div_eq_mul_inv, zpow_ofNat]
  rw [hid, intervalIntegral.integral_const_mul, hz]
  norm_num [inv_pow, zpow_ofNat]
  ring

private theorem integral_two_mul_div {C K : ℝ} (hK : 1 ≤ K) :
    (∫ t in (1 : ℝ)..K, (2 * C) / t) = 2 * C * Real.log K := by
  have hnot : (0 : ℝ) ∉ Set.uIcc 1 K := by
    rw [uIcc_of_le hK]
    norm_num
  have hid : (fun t : ℝ ↦ (2 * C) / t) = fun t ↦ (2 * C) * t⁻¹ := by
    funext t
    rw [div_eq_mul_inv]
  rw [hid, intervalIntegral.integral_const_mul, integral_inv hnot, div_one]

/-- A quadratic initial-segment count gives a logarithmic reciprocal-square
sum, by integrating the counting function against `2/t^3`. -/
theorem finite_sum_reciprocal_square_le_of_quadratic_count
    {ι : Type*} (S : Finset ι) (r : ι → ℝ) (C K : ℝ) (hK : 1 ≤ K)
    (hr : ∀ i ∈ S, 1 ≤ r i) (hrK : ∀ i ∈ S, r i ≤ K)
    (hcount : ∀ T : ℝ, 1 ≤ T →
      ((S.filter fun i ↦ r i ≤ T).card : ℝ) ≤ C * T ^ (2 : ℕ)) :
    (∑ i ∈ S, 1 / r i ^ (2 : ℕ)) ≤ C + 2 * C * Real.log K := by
  classical
  let k : ι → ℝ → ℝ := fun i ↦ (Ioi (r i)).indicator (fun t : ℝ ↦ 2 / t ^ (3 : ℕ))
  have hbase : IntegrableOn (fun t : ℝ ↦ 2 / t ^ (3 : ℕ)) (Icc 1 K) := by
    apply ContinuousOn.integrableOn_Icc
    exact continuousOn_const.div (continuousOn_id.pow 3)
      (fun t ht ↦ pow_ne_zero _ (by linarith [ht.1]))
  have hk (i : ι) : IntegrableOn (k i) (Icc 1 K) := hbase.indicator measurableSet_Ioi
  have hmajor : IntegrableOn (fun t : ℝ ↦ (2 * C) / t) (Icc 1 K) := by
    apply ContinuousOn.integrableOn_Icc
    exact continuousOn_const.div continuousOn_id (fun t ht ↦ by linarith [ht.1])
  have hpoint (t : ℝ) (ht : t ∈ Icc (1 : ℝ) K) :
      (∑ i ∈ S, k i t) ≤ (2 * C) / t := by
    have htpos : 0 < t := by linarith [ht.1]
    have hc : ((S.filter fun i ↦ r i < t).card : ℝ) ≤ C * t ^ (2 : ℕ) := by
      refine le_trans ?_ (hcount t ht.1)
      exact_mod_cast Finset.card_le_card (show (S.filter fun i ↦ r i < t) ⊆
        (S.filter fun i ↦ r i ≤ t) from fun i hi ↦ by
          simp only [Finset.mem_filter] at hi ⊢
          exact ⟨hi.1, hi.2.le⟩)
    have heq : (∑ i ∈ S, k i t) =
        ((S.filter fun i ↦ r i < t).card : ℝ) * (2 / t ^ (3 : ℕ)) := by
      simp [k, Set.indicator_apply, ← Finset.sum_filter]
    rw [heq]
    calc
      _ ≤ (C * t ^ (2 : ℕ)) * (2 / t ^ (3 : ℕ)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by field_simp
  have hint := setIntegral_mono_on (integrable_finset_sum S (fun i _ ↦ hk i)) hmajor
    measurableSet_Icc hpoint
  have hki (i : ι) (hi : i ∈ S) :
      (∫ t : ℝ in Icc 1 K, k i t) = 1 / r i ^ (2 : ℕ) - 1 / K ^ (2 : ℕ) := by
    have hri : 0 < r i := by linarith [hr i hi]
    have hinter : Icc (1 : ℝ) K ∩ Ioi (r i) = Ioc (r i) K := by
      ext t
      simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨⟨_, htK⟩, hrt⟩
        exact ⟨hrt, htK⟩
      · rintro ⟨hrt, htK⟩
        exact ⟨⟨(hr i hi).trans hrt.le, htK⟩, hrt⟩
    rw [show k i = (Ioi (r i)).indicator (fun t : ℝ ↦ 2 / t ^ (3 : ℕ)) by rfl,
      setIntegral_indicator measurableSet_Ioi, hinter,
      ← intervalIntegral.integral_of_le (hrK i hi), integral_two_div_cube hri (hrK i hi)]
  have hid : (∑ i ∈ S, 1 / r i ^ (2 : ℕ)) =
      (S.card : ℝ) / K ^ (2 : ℕ) + ∫ t : ℝ in Icc 1 K, ∑ i ∈ S, k i t := by
    rw [integral_finset_sum S (fun i _ ↦ hk i)]
    rw [Finset.sum_congr rfl (fun i hi ↦ hki i hi)]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have hfilter : S.filter (fun i ↦ r i ≤ K) = S := Finset.filter_eq_self.mpr hrK
  have hcard : (S.card : ℝ) / K ^ (2 : ℕ) ≤ C := by
    apply (div_le_iff₀ (by positivity : 0 < K ^ (2 : ℕ))).2
    simpa only [hfilter] using hcount K hK
  have heval : (∫ t : ℝ in Icc 1 K, (2 * C) / t) = 2 * C * Real.log K := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hK,
      integral_two_mul_div hK]
  rw [hid]
  rw [heval] at hint
  exact add_le_add hcard hint

/-- An explicit finite square containing every integer direction of
Euclidean size at most `K`. -/
def integerDirectionsEuclideanBox (K : ℝ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-⌈K⌉ : ℤ) ⌈K⌉).product (Finset.Icc (-⌈K⌉ : ℤ) ⌈K⌉)

/-- The exact full finite set of nonzero integer vectors of Euclidean size at most `K`. -/
def integerDirectionsEuclideanUpTo (K : ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact (integerDirectionsEuclideanBox K).filter (fun d ↦ d ≠ (0, 0) ∧ intEuclidean d ≤ K)

theorem integerDirection_mem_euclideanBox {d : ℤ × ℤ} {K : ℝ}
    (hd : intEuclidean d ≤ K) : d ∈ integerDirectionsEuclideanBox K := by
  have hx := (intEuclidean_coordinate_bounds d).1.trans (hd.trans (Int.le_ceil K))
  have hy := (intEuclidean_coordinate_bounds d).2.trans (hd.trans (Int.le_ceil K))
  have hx' : -⌈K⌉ ≤ d.1 ∧ d.1 ≤ ⌈K⌉ := by exact_mod_cast abs_le.mp hx
  have hy' : -⌈K⌉ ≤ d.2 ∧ d.2 ≤ ⌈K⌉ := by exact_mod_cast abs_le.mp hy
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hx', Finset.mem_Icc.mpr hy'⟩

@[simp] theorem mem_integerDirectionsEuclideanUpTo (K : ℝ) (d : ℤ × ℤ) :
    d ∈ integerDirectionsEuclideanUpTo K ↔ d ≠ (0, 0) ∧ intEuclidean d ≤ K := by
  classical
  simp only [integerDirectionsEuclideanUpTo, Finset.mem_filter]
  exact ⟨And.right, fun hd ↦ ⟨integerDirection_mem_euclideanBox hd.2, hd⟩⟩

/-- The number of integer directions in any finite family below radius
`T` is bounded by a fixed quadratic count. Zero may be included here. -/
theorem finite_integer_direction_count_le_quadratic (S : Finset (ℤ × ℤ))
    (T : ℝ) (hT : 1 ≤ T) :
    ((S.filter fun d ↦ intEuclidean d ≤ T).card : ℝ) ≤ 25 * T ^ (2 : ℕ) := by
  classical
  have hsub : (S.filter fun d ↦ intEuclidean d ≤ T) ⊆ integerDirectionsEuclideanBox T := by
    intro d hd
    exact integerDirection_mem_euclideanBox (Finset.mem_filter.mp hd).2
  have hceil : (0 : ℤ) ≤ ⌈T⌉ := Int.ceil_nonneg (by linarith)
  have hcZ : ((Finset.Icc (-⌈T⌉ : ℤ) ⌈T⌉).card : ℤ) = 2 * ⌈T⌉ + 1 := by
    rw [Int.card_Icc_of_le (a := (-⌈T⌉ : ℤ)) (b := ⌈T⌉) (by omega)]
    ring
  have hcR : ((Finset.Icc (-⌈T⌉ : ℤ) ⌈T⌉).card : ℝ) = 2 * (⌈T⌉ : ℝ) + 1 := by
    exact_mod_cast hcZ
  have hbox : ((integerDirectionsEuclideanBox T).card : ℝ) =
      (2 * (⌈T⌉ : ℝ) + 1) ^ (2 : ℕ) := by
    rw [integerDirectionsEuclideanBox, Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul, hcR]
    ring
  have hceilR : (0 : ℝ) ≤ ⌈T⌉ := by exact_mod_cast hceil
  have hA : 2 * (⌈T⌉ : ℝ) + 1 ≤ 5 * T := by linarith [Int.ceil_lt_add_one T]
  calc
    _ ≤ ((integerDirectionsEuclideanBox T).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = (2 * (⌈T⌉ : ℝ) + 1) ^ (2 : ℕ) := hbox
    _ ≤ (5 * T) ^ (2 : ℕ) :=
      (sq_le_sq₀ (by linarith : 0 ≤ 2 * (⌈T⌉ : ℝ) + 1) (by linarith : 0 ≤ 5 * T)).mpr hA
    _ = 25 * T ^ (2 : ℕ) := by ring

/-- A genuinely logarithmic reciprocal-square bound for any finite family
of nonzero integer vectors in the Euclidean radius `K`. -/
theorem finite_integer_reciprocal_square_le_log
    (S : Finset (ℤ × ℤ)) (K : ℝ) (hK : 1 ≤ K)
    (hn : ∀ d ∈ S, d ≠ (0, 0)) (hsize : ∀ d ∈ S, intEuclidean d ≤ K) :
    (∑ d ∈ S, 1 / intEuclidean d ^ (2 : ℕ)) ≤ 50 * Real.log (2 * K) := by
  have hbase := finite_sum_reciprocal_square_le_of_quadratic_count S intEuclidean 25 K hK
    (fun d hd ↦ intEuclidean_ge_one d (hn d hd)) hsize
    (fun T hT ↦ finite_integer_direction_count_le_quadratic S T hT)
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    linarith
  have hlog : Real.log (2 * K) = Real.log 2 + Real.log K :=
    Real.log_mul (by norm_num) (by linarith : K ≠ 0)
  rw [hlog]
  nlinarith

/-- The full nonzero standard lattice reciprocal-square sum grows at most logarithmically. -/
theorem integerDirectionsEuclideanUpTo_reciprocal_square_le_log
    (K : ℝ) (hK : 1 ≤ K) :
    (∑ d ∈ integerDirectionsEuclideanUpTo K, 1 / intEuclidean d ^ (2 : ℕ)) ≤
      50 * Real.log (2 * K) := by
  apply finite_integer_reciprocal_square_le_log _ K hK
  · intro d hd
    exact ((mem_integerDirectionsEuclideanUpTo K d).mp hd).1
  · intro d hd
    exact ((mem_integerDirectionsEuclideanUpTo K d).mp hd).2

end Markov
