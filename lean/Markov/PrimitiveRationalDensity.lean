import Markov.TraceRationalParameters
import Mathlib.Topology.Instances.Rat
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

/-! Density of primitive rational parameters on the actual four chord charts.
This uses integer coordinate changes only, with no symmetry assumption for the norm. -/

noncomputable section
open Set

namespace Markov

/-- Every nonempty subinterval of the unit parameter interval contains a
primitive direction with both integer coordinates strictly positive. -/
theorem exists_positive_primitive_profileParameter_between {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ p : ℤ × ℤ, 0 < p.1 ∧ 0 < p.2 ∧ IsCoprime p.1 p.2 ∧
      a < profileParameter p ∧ profileParameter p < b := by
  obtain ⟨r, hra, hrb⟩ := exists_rat_btwn hab
  have hr0 : (0 : ℚ) < r := by exact_mod_cast ha.trans_lt hra
  have hnum : 0 < r.num := Rat.num_pos.mpr hr0
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hnumlt : (r.num : ℝ) < r.den := by
    apply (div_lt_one hden).1
    simpa only [← Rat.cast_def] using hrb.trans_le hb
  have hfirst : 0 < (r.den : ℤ) - r.num := by
    exact_mod_cast sub_pos.mpr hnumlt
  have hcop : IsCoprime r.num (r.den : ℤ) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [Int.natAbs_natCast] using r.reduced
  have hdiffcop : IsCoprime ((r.den : ℤ) - r.num) r.num := by
    obtain ⟨c, d, hcd⟩ := hcop
    refine ⟨d, c + d, ?_⟩
    linear_combination hcd
  have hparam : profileParameter ((r.den : ℤ) - r.num, r.num) = (r : ℝ) := by
    simp [profileParameter, profileMass, Rat.cast_def]
  exact ⟨((r.den : ℤ) - r.num, r.num), hfirst, hnum, hdiffcop,
    hparam ▸ hra, hparam ▸ hrb⟩

/-- The primitive profile parameters meet every open subinterval of `[0,1]`. -/
theorem exists_nonnegativePrimitive_profileParameter_between {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ p : ℤ × ℤ, NonnegativePrimitiveDirection p ∧
      a < profileParameter p ∧ profileParameter p < b := by
  obtain ⟨p, hp0, hp1, hpc, hpa, hpb⟩ :=
    exists_positive_primitive_profileParameter_between ha hab hb
  exact ⟨p, ⟨hp0.le, hp1.le, hpc⟩, hpa, hpb⟩

/-- Reconstructing a direction in a quarter-turn frame recovers its coordinates. -/
theorem quadrantCoordinates_seededDirection (k : Fin 4) (p : ℤ × ℤ) :
    quadrantCoordinates k
      (seededDirection (quadrantSeedDirections k).1 (quadrantSeedDirections k).2 p) = p := by
  fin_cases k <;> ext <;>
    simp [quadrantCoordinates, quadrantSeedDirections, seededDirection]

/-- Primitivity of coordinates is equivalent to primitivity of the actual direction. -/
theorem quadrantCoordinates_coprime_iff (k : Fin 4) (p : ℤ × ℤ) :
    IsCoprime (quadrantCoordinates k p).1 (quadrantCoordinates k p).2 ↔
      IsCoprime p.1 p.2 := by
  refine ⟨?_, quadrantCoordinates_coprime k p⟩
  intro hp
  fin_cases k <;> simp only [quadrantCoordinates] at hp
  · exact hp
  · simpa only [neg_neg] using hp.neg_right.symm
  · simpa only [neg_neg] using hp.neg_neg
  · simpa only [neg_neg] using hp.neg_left.symm

/-- Primitive integer labels are dense in the local parameter of every actual quarter. -/
theorem exists_primitive_traceRationalQuarterParameter_between (k : Fin 4) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ p : ℤ × ℤ, IsCoprime p.1 p.2 ∧
      0 < (quadrantCoordinates k p).1 ∧ 0 < (quadrantCoordinates k p).2 ∧
      a < traceRationalQuarterParameter k p ∧ traceRationalQuarterParameter k p < b := by
  obtain ⟨v, hv0, hv1, hvc, hva, hvb⟩ :=
    exists_positive_primitive_profileParameter_between ha hab hb
  let p := seededDirection (quadrantSeedDirections k).1 (quadrantSeedDirections k).2 v
  have hp : quadrantCoordinates k p = v := quadrantCoordinates_seededDirection k v
  refine ⟨p, (quadrantCoordinates_coprime_iff k p).mp (hp ▸ hvc), ?_⟩
  simp only [traceRationalQuarterParameter, hp]
  exact ⟨hv0, hv1, hva, hvb⟩

/-- The dense local parameters also lie strictly inside every corresponding global quarter. -/
theorem exists_primitive_traceRationalParameter_between_in_quarter
    (k : Fin 4) {a b : ℝ} (ha : (k.val : ℝ) ≤ a) (hab : a < b)
    (hb : b ≤ (k.val : ℝ) + 1) :
    ∃ p : ℤ × ℤ, IsCoprime p.1 p.2 ∧
      0 < (quadrantCoordinates k p).1 ∧ 0 < (quadrantCoordinates k p).2 ∧
      a < traceRationalParameter k p ∧ traceRationalParameter k p < b := by
  obtain ⟨p, hpc, hp0, hp1, hpa, hpb⟩ :=
    exists_primitive_traceRationalQuarterParameter_between k
      (show 0 ≤ a - (k.val : ℝ) by linarith)
      (show a - (k.val : ℝ) < b - (k.val : ℝ) by linarith)
      (show b - (k.val : ℝ) ≤ 1 by linarith)
  refine ⟨p, hpc, hp0, hp1, ?_, ?_⟩ <;>
    dsimp [traceRationalParameter] <;> linarith

/-- Every nonempty interval in the full actual path contains a primitive
parameter strictly inside one of the four quarter charts. -/
theorem exists_primitive_traceRationalParameter_between {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 4) :
    ∃ (k : Fin 4) (p : ℤ × ℤ), IsCoprime p.1 p.2 ∧
      0 < (quadrantCoordinates k p).1 ∧ 0 < (quadrantCoordinates k p).2 ∧
      a < traceRationalParameter k p ∧ traceRationalParameter k p < b := by
  have hlocal (k : Fin 4) (hka : (k.val : ℝ) ≤ a) (hak : a < (k.val : ℝ) + 1) :
      ∃ (k : Fin 4) (p : ℤ × ℤ), IsCoprime p.1 p.2 ∧
        0 < (quadrantCoordinates k p).1 ∧ 0 < (quadrantCoordinates k p).2 ∧
        a < traceRationalParameter k p ∧ traceRationalParameter k p < b := by
    obtain ⟨p, hpc, hp0, hp1, hpa, hpb⟩ :=
      exists_primitive_traceRationalParameter_between_in_quarter k hka
        (lt_min hab hak) (min_le_right b ((k.val : ℝ) + 1))
    exact ⟨k, p, hpc, hp0, hp1, hpa, hpb.trans_le (min_le_left _ _)⟩
  by_cases ha1 : a < 1
  · exact hlocal 0 (by simpa using ha) (by simpa using ha1)
  · by_cases ha2 : a < 2
    · exact hlocal 1 (by norm_num; linarith) (by norm_num; exact ha2)
    · by_cases ha3 : a < 3
      · exact hlocal 2 (by norm_num; linarith) (by norm_num; exact ha3)
      · exact hlocal 3 (by norm_num; linarith)
          (by norm_num; linarith)

end Markov
