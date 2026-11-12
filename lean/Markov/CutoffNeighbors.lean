import Markov.PrimitivePartner
import Markov.FareyScale

/-! Arithmetic adjacency in the actual finite denominator cutoff.
The points `(p,q)` represent the slopes `q/p` in `[0,1]`.
Consecutiveness means that no primitive cutoff point has a strictly
intermediate slope; it does not assume a determinant-one condition.
No geometric correspondence with a surface is asserted here. -/

noncomputable section
namespace Markov

/-- The actual finite set of primitive slopes with positive denominator at most `H`. -/
def cutoffSlopesUpTo (H : ℕ) : Finset (ℤ × ℤ) := by
  classical
  exact ((Finset.Icc 1 (H : ℤ)).product (Finset.Icc 0 (H : ℤ))).filter
    (fun u => u.2 ≤ u.1 ∧ IsCoprime u.1 u.2)

theorem mem_cutoffSlopesUpTo (H : ℕ) (u : ℤ × ℤ) :
    u ∈ cutoffSlopesUpTo H ↔
      0 < u.1 ∧ 0 ≤ u.2 ∧ u.2 ≤ u.1 ∧ u.1 ≤ H ∧ IsCoprime u.1 u.2 := by
  classical
  simp only [cutoffSlopesUpTo, Finset.mem_filter, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, hH⟩, h2, _⟩, h21, hcop⟩
    exact ⟨by omega, h2, h21, hH, hcop⟩
  · rintro ⟨h1, h2, h21, hH, hcop⟩
    exact ⟨⟨⟨by omega, hH⟩, h2, h21.trans hH⟩, h21, hcop⟩

/-- Real slope of an integral denominator/numerator pair. -/
def cutoffSlope (u : ℤ × ℤ) : ℝ := (u.2 : ℝ) / (u.1 : ℝ)

/-- For positive denominators, determinant order is the actual slope order. -/
theorem cutoffSlope_lt_iff_intDet_pos (u v : ℤ × ℤ)
    (hu : 0 < u.1) (hv : 0 < v.1) :
    cutoffSlope u < cutoffSlope v ↔ 0 < intDet u v := by
  have hu' : (0 : ℝ) < u.1 := by exact_mod_cast hu
  have hv' : (0 : ℝ) < v.1 := by exact_mod_cast hv
  rw [cutoffSlope, cutoffSlope, div_lt_div_iff₀ hu' hv']
  constructor
  · intro h
    have hi : u.2 * v.1 < v.2 * u.1 := by exact_mod_cast h
    dsimp [intDet]
    nlinarith
  · intro h
    have hi : u.2 * v.1 < v.2 * u.1 := by
      dsimp [intDet] at h
      nlinarith
    exact_mod_cast hi

/-- Ordered, consecutive elements of the actual cutoff set. With positive
 denominators, positivity of `intDet u v` says precisely `u.2/u.1 < v.2/v.1`. -/
def ConsecutiveCutoffSlopes (H : ℕ) (u v : ℤ × ℤ) : Prop :=
  u ∈ cutoffSlopesUpTo H ∧ v ∈ cutoffSlopesUpTo H ∧ 0 < intDet u v ∧
    ∀ w ∈ cutoffSlopesUpTo H, ¬(0 < intDet u w ∧ 0 < intDet w v)

/-- The consecutiveness definition is exactly absence of a strictly
 intermediate real slope in the actual finite primitive cutoff set. -/
theorem consecutiveCutoffSlopes_iff_slope (H : ℕ) (u v : ℤ × ℤ) :
    ConsecutiveCutoffSlopes H u v ↔
      u ∈ cutoffSlopesUpTo H ∧ v ∈ cutoffSlopesUpTo H ∧
      cutoffSlope u < cutoffSlope v ∧
      ∀ w ∈ cutoffSlopesUpTo H,
        ¬(cutoffSlope u < cutoffSlope w ∧ cutoffSlope w < cutoffSlope v) := by
  constructor
  · rintro ⟨hu, hv, huv, hbetween⟩
    have hup := ((mem_cutoffSlopesUpTo H u).mp hu).1
    have hvp := ((mem_cutoffSlopesUpTo H v).mp hv).1
    refine ⟨hu, hv, (cutoffSlope_lt_iff_intDet_pos u v hup hvp).mpr huv, ?_⟩
    intro w hw hmid
    have hwp := ((mem_cutoffSlopesUpTo H w).mp hw).1
    exact hbetween w hw ⟨(cutoffSlope_lt_iff_intDet_pos u w hup hwp).mp hmid.1,
      (cutoffSlope_lt_iff_intDet_pos w v hwp hvp).mp hmid.2⟩
  · rintro ⟨hu, hv, huv, hbetween⟩
    have hup := ((mem_cutoffSlopesUpTo H u).mp hu).1
    have hvp := ((mem_cutoffSlopesUpTo H v).mp hv).1
    refine ⟨hu, hv, (cutoffSlope_lt_iff_intDet_pos u v hup hvp).mp huv, ?_⟩
    intro w hw hmid
    have hwp := ((mem_cutoffSlopesUpTo H w).mp hw).1
    exact hbetween w hw ⟨(cutoffSlope_lt_iff_intDet_pos u w hup hwp).mpr hmid.1,
      (cutoffSlope_lt_iff_intDet_pos w v hwp hvp).mpr hmid.2⟩

private theorem cutoff_bounded_right_partner (u : ℤ × ℤ)
    (hp : 0 < u.1) (hq : 0 ≤ u.2) (hqp : u.2 < u.1)
    (hcop : IsCoprime u.1 u.2) :
    ∃ v : ℤ × ℤ, 0 < v.1 ∧ 0 ≤ v.2 ∧ v.2 ≤ v.1 ∧ v.1 ≤ u.1 ∧
      intDet u v = 1 := by
  by_cases hq0 : u.2 = 0
  · have hu : IsUnit u.1 := isCoprime_zero_right.mp (by simpa only [hq0] using hcop)
    have hp1 : u.1 = 1 := by
      simpa only [abs_of_pos hp] using Int.isUnit_iff_abs_eq.mp hu
    exact ⟨(1, 1), by norm_num, by norm_num, by norm_num, by omega,
      by simp [intDet, hp1, hq0]⟩
  · obtain ⟨c, d, hc, hcp, hd, hdq, hdet⟩ :=
      positive_coprime_bounded_partner u.1 u.2 hp (by omega) hcop
    have hp2 : 2 ≤ u.1 := by omega
    have hcpos : 0 < c := by
      by_contra hn
      have hc0 : c = 0 := by omega
      have hm := mul_le_mul_of_nonneg_left hd hp.le
      nlinarith
    have hdc : d ≤ c := by
      by_contra hn
      have hm := mul_le_mul_of_nonneg_left (show c + 1 ≤ d by omega) hp.le
      have hn := mul_nonneg (show 0 ≤ u.1 - u.2 by omega) hc
      nlinarith
    exact ⟨(c, d), hcpos, by omega, hdc, by omega, hdet⟩

/-- Every nonfinal cutoff fraction has a determinant-one right partner in
 the cutoff whose next shear already exceeds the denominator bound. -/
theorem cutoff_exists_maximal_right_partner (H : ℕ) (u : ℤ × ℤ)
    (hu : u ∈ cutoffSlopesUpTo H) (hlt : u.2 < u.1) :
    ∃ w ∈ cutoffSlopesUpTo H, intDet u w = 1 ∧ (H : ℤ) < u.1 + w.1 := by
  obtain ⟨hp, hq, _, hpH, hcop⟩ := (mem_cutoffSlopesUpTo H u).mp hu
  obtain ⟨v, hvp, hvq, hvqp, hvpu, hdet⟩ :=
    cutoff_bounded_right_partner u hp hq hlt hcop
  let k : ℤ := ((H : ℤ) - v.1) / u.1
  let w : ℤ × ℤ := (v.1 + k * u.1, v.2 + k * u.2)
  have hk : 0 ≤ k := Int.ediv_nonneg (by omega) hp.le
  have hrem0 : 0 ≤ ((H : ℤ) - v.1) % u.1 := Int.emod_nonneg _ hp.ne'
  have hrem : ((H : ℤ) - v.1) % u.1 < u.1 := Int.emod_lt_of_pos _ hp
  have hdiv : u.1 * k + ((H : ℤ) - v.1) % u.1 = (H : ℤ) - v.1 :=
    Int.mul_ediv_add_emod _ _
  have hwp : 0 < w.1 := by
    dsimp [w]
    nlinarith [mul_nonneg hk hp.le]
  have hwq : 0 ≤ w.2 := by
    dsimp [w]
    nlinarith [mul_nonneg hk hq]
  have hwqp : w.2 ≤ w.1 := by
    dsimp [w]
    nlinarith [mul_nonneg hk (show 0 ≤ u.1 - u.2 by omega)]
  have hwH : w.1 ≤ H := by dsimp [w]; nlinarith
  have hwH' : (H : ℤ) < u.1 + w.1 := by dsimp [w]; nlinarith
  have hdet' : intDet u w = 1 := by
    dsimp [intDet, w] at *
    nlinarith
  have hwcop : IsCoprime w.1 w.2 := by
    refine ⟨-u.2, u.1, ?_⟩
    dsimp [intDet] at hdet'
    nlinarith
  exact ⟨w, (mem_cutoffSlopesUpTo H w).mpr ⟨hwp, hwq, hwqp, hwH, hwcop⟩,
    hdet', hwH'⟩

/-- Actual consecutive primitive cutoff slopes have determinant one, and
 the sum of their denominators exceeds the cutoff. -/
theorem consecutiveCutoffSlopes_det_and_denominator_sum (H : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H u v) :
    intDet u v = 1 ∧ (H : ℤ) < u.1 + v.1 := by
  rcases h with ⟨hu, hv, huv, hbetween⟩
  obtain ⟨hup, huq, huqp, _, _⟩ := (mem_cutoffSlopesUpTo H u).mp hu
  obtain ⟨hvp, _, hvqp, hvH, hvcop⟩ := (mem_cutoffSlopesUpTo H v).mp hv
  have hult : u.2 < u.1 := by
    by_contra hn
    have he : u.2 = u.1 := by omega
    have hm := mul_nonneg hup.le (show 0 ≤ v.1 - v.2 by omega)
    dsimp [intDet] at huv
    nlinarith
  obtain ⟨w, hw, huw, hHw⟩ := cutoff_exists_maximal_right_partner H u hu hult
  obtain ⟨hwp, _, _, _, _⟩ := (mem_cutoffSlopesUpTo H w).mp hw
  have hcoord1 : v.1 = intDet u v * w.1 - intDet w v * u.1 := by
    dsimp [intDet] at *
    linear_combination -v.1 * huw
  have hcoord2 : v.2 = intDet u v * w.2 - intDet w v * u.2 := by
    dsimp [intDet] at *
    linear_combination -v.2 * huw
  have hwvnonneg : 0 ≤ intDet w v := by
    by_contra hn
    have he : intDet w v ≤ -1 := by omega
    have hm1 := mul_le_mul_of_nonneg_right (show 1 ≤ intDet u v by omega) hwp.le
    have hm2 := mul_le_mul_of_nonneg_right he hup.le
    nlinarith
  have hwv : intDet w v = 0 := by
    by_contra hn
    exact hbetween w hw ⟨by omega, by omega⟩
  have hcoord1' : v.1 = intDet u v * w.1 := by simpa only [hwv, zero_mul, sub_zero] using hcoord1
  have hcoord2' : v.2 = intDet u v * w.2 := by simpa only [hwv, zero_mul, sub_zero] using hcoord2
  obtain ⟨s, t, hbez⟩ := hvcop
  have hdiv : intDet u v ∣ 1 := by
    refine ⟨s * w.1 + t * w.2, ?_⟩
    rw [hcoord1', hcoord2'] at hbez
    nlinarith [hbez]
  have habs : |intDet u v| = 1 := Int.isUnit_iff_abs_eq.mp (isUnit_of_dvd_one hdiv)
  have hd : intDet u v = 1 := by simpa only [abs_of_pos huv] using habs
  refine ⟨hd, ?_⟩
  have hvw : v.1 = w.1 := by simpa only [hd, one_mul] using hcoord1'
  simpa only [hvw] using hHw

/-- The absolute determinant form used in the cutoff slope-spacing estimate. -/
theorem consecutiveCutoffSlopes_abs_det (H : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H u v) : |u.1 * v.2 - u.2 * v.1| = 1 := by
  have hd := (consecutiveCutoffSlopes_det_and_denominator_sum H u v h).1
  change |intDet u v| = 1
  rw [hd]
  norm_num

/-- Exact spacing for actual consecutive primitive cutoff slopes. -/
theorem consecutiveCutoffSlopes_gap (H : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H u v) :
    |cutoffSlope u - cutoffSlope v| = 1 / ((u.1 : ℝ) * (v.1 : ℝ)) := by
  have hup : (0 : ℝ) < u.1 := by
    exact_mod_cast ((mem_cutoffSlopesUpTo H u).mp h.1).1
  have hvp : (0 : ℝ) < v.1 := by
    exact_mod_cast ((mem_cutoffSlopesUpTo H v).mp h.2.1).1
  have hd : |(u.1 : ℝ) * v.2 - (u.2 : ℝ) * v.1| = 1 := by
    exact_mod_cast consecutiveCutoffSlopes_abs_det H u v h
  exact farey_slope_gap _ _ _ _ hup hvp hd

/-- The denominator scale in v1 Lemma 3 now follows for the actual cutoff
 neighbors, without assuming their determinant or denominator-sum properties. -/
theorem consecutiveCutoffSlopes_gap_le_scale (H : ℕ) (u v : ℤ × ℤ)
    (h : ConsecutiveCutoffSlopes H u v) :
    |cutoffSlope u - cutoffSlope v| ≤
      2 / ((H : ℝ) * min (u.1 : ℝ) (v.1 : ℝ)) := by
  obtain ⟨hup, _, _, huH, _⟩ := (mem_cutoffSlopesUpTo H u).mp h.1
  have hvp := ((mem_cutoffSlopesUpTo H v).mp h.2.1).1
  have hH : (0 : ℝ) < H := by
    have : (0 : ℤ) < H := hup.trans_le huH
    exact_mod_cast this
  have hsum : (H : ℝ) < (u.1 : ℝ) + v.1 := by
    exact_mod_cast (consecutiveCutoffSlopes_det_and_denominator_sum H u v h).2
  rw [consecutiveCutoffSlopes_gap H u v h]
  exact farey_reciprocal_scale _ _ _ (by exact_mod_cast hup)
    (by exact_mod_cast hvp) hH hsum

end Markov
