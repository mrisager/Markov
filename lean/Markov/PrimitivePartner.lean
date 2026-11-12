import Markov.FareyHolonomy
import Mathlib.Data.Int.Order.Units

/-! Bounded nonnegative unimodular partners for primitive integral vectors.
The interior case uses Bezout followed by reduction modulo the first
coordinate. Axis cases are treated explicitly. -/

namespace Markov

/-- A positive primitive vector has a right Farey neighbour in its coordinate
box. The first coordinate is strictly smaller and the second is positive. -/
theorem positive_coprime_bounded_partner (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hcop : IsCoprime a b) :
    ∃ c d : ℤ, 0 ≤ c ∧ c < a ∧ 1 ≤ d ∧ d ≤ b ∧ a * d - b * c = 1 := by
  obtain ⟨s, t, hbez⟩ := hcop
  let c : ℤ := (-t) % a
  let k : ℤ := (-t) / a
  let d : ℤ := s - b * k
  have hc : 0 ≤ c := Int.emod_nonneg _ ha.ne'
  have hca : c < a := Int.emod_lt_of_pos _ ha
  have hmod : a * k + c = -t := Int.mul_ediv_add_emod _ _
  have hdet : a * d - b * c = 1 := by
    dsimp [d]
    linear_combination hbez - b * hmod
  have hdpos : 1 ≤ d := by
    by_contra hd
    have hd0 : d ≤ 0 := by omega
    have hprod : a * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hd0
    have hbc : 0 ≤ b * c := mul_nonneg hb.le hc
    omega
  have hdb : d ≤ b := by
    have hca' : c ≤ a - 1 := by omega
    have hbc : b * c ≤ b * (a - 1) := mul_le_mul_of_nonneg_left hca' hb.le
    nlinarith
  exact ⟨c, d, hc, hca, hdpos, hdb, hdet⟩

/-- The only nonnegative primitive vectors on the coordinate axes are the
two standard basis vectors. -/
theorem nonnegative_primitive_axis (p : ℤ × ℤ) (hp0 : 0 ≤ p.1) (hp1 : 0 ≤ p.2)
    (hcop : IsCoprime p.1 p.2) (haxis : p.1 = 0 ∨ p.2 = 0) :
    p = (1, 0) ∨ p = (0, 1) := by
  rcases haxis with hx | hy
  · have hu : IsUnit p.2 := isCoprime_zero_left.mp (by simpa only [hx] using hcop)
    have hb : p.2 = 1 := by
      simpa only [abs_of_nonneg hp1] using Int.isUnit_iff_abs_eq.mp hu
    right
    exact Prod.ext hx hb
  · have hu : IsUnit p.1 := isCoprime_zero_right.mp (by simpa only [hy] using hcop)
    have ha : p.1 = 1 := by
      simpa only [abs_of_nonneg hp0] using Int.isUnit_iff_abs_eq.mp hu
    left
    exact Prod.ext ha hy

/-- Every nonnegative primitive direction lies in a nonnegative unimodular
pair, with the partner coordinates bounded by the original coordinates or 1.
The orientation choice is necessary for the vertical axis direction. -/
theorem nonnegative_primitive_bounded_partner (p : ℤ × ℤ)
    (hp0 : 0 ≤ p.1) (hp1 : 0 ≤ p.2) (hcop : IsCoprime p.1 p.2) :
    ∃ q : ℤ × ℤ, 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 ≤ max p.1 1 ∧ q.2 ≤ max p.2 1 ∧
      (intDet p q = 1 ∨ intDet q p = 1) := by
  by_cases haxis : p.1 = 0 ∨ p.2 = 0
  · rcases nonnegative_primitive_axis p hp0 hp1 hcop haxis with rfl | rfl
    · refine ⟨(0, 1), ?_⟩
      norm_num [intDet]
    · refine ⟨(1, 0), ?_⟩
      norm_num [intDet]
  · push_neg at haxis
    obtain ⟨c, d, hc, hca, hd, hdb, hdet⟩ :=
      positive_coprime_bounded_partner p.1 p.2 (lt_of_le_of_ne hp0 haxis.1.symm)
        (lt_of_le_of_ne hp1 haxis.2.symm) hcop
    refine ⟨(c, d), hc, by omega, ?_, ?_, Or.inl hdet⟩
    · exact hca.le.trans (le_max_left _ _)
    · exact hdb.trans (le_max_left _ _)

/-- A form directly consumable by a coverage theorem for nonnegative
unimodular pairs. -/
theorem nonnegative_primitive_in_unimodular_pair (p : ℤ × ℤ)
    (hp0 : 0 ≤ p.1) (hp1 : 0 ≤ p.2) (hcop : IsCoprime p.1 p.2) :
    ∃ u v : ℤ × ℤ, 0 ≤ u.1 ∧ 0 ≤ u.2 ∧ 0 ≤ v.1 ∧ 0 ≤ v.2 ∧
      intDet u v = 1 ∧ (p = u ∨ p = v) := by
  obtain ⟨q, hq0, hq1, _, _, hd | hd⟩ :=
    nonnegative_primitive_bounded_partner p hp0 hp1 hcop
  · exact ⟨p, q, hp0, hp1, hq0, hq1, hd, Or.inl rfl⟩
  · exact ⟨q, p, hq0, hq1, hp0, hp1, hd, Or.inr rfl⟩

end Markov
