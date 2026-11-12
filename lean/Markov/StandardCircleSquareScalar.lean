import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Tactic

noncomputable section
namespace Markov

/-- Scalar coordinate map from the closed square to the standard unit additive circle. -/
def standardCircleSquareScalar (a : ℝ) : AddCircle (1 : ℝ) :=
  (((a+1)/2 : ℝ) : AddCircle (1 : ℝ))

theorem standardCircleSquareScalar_neg_one : standardCircleSquareScalar (-1) = 0 := by
  norm_num [standardCircleSquareScalar]

theorem standardCircleSquareScalar_one : standardCircleSquareScalar 1 = 0 := by
  norm_num [standardCircleSquareScalar, AddCircle.coe_period]

/-- Every standard circle class is represented by a scalar in the closed square interval. -/
theorem standardCircleSquareScalar_surjective (c : AddCircle (1 : ℝ)) :
    ∃ a ∈ Set.Icc (-1 : ℝ) 1, standardCircleSquareScalar a = c := by
  obtain ⟨t, ht, hc⟩ := AddCircle.eq_coe_Ico c
  refine ⟨2*t-1, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  unfold standardCircleSquareScalar
  convert hc using 1
  congr 1
  ring

/-- Exactly the two endpoints map to the zero circle class. -/
theorem standardCircleSquareScalar_eq_zero_iff {a : ℝ}
    (ha : a ∈ Set.Icc (-1 : ℝ) 1) :
    standardCircleSquareScalar a = 0 ↔ a = -1 ∨ a = 1 := by
  by_cases h1 : a = 1
  · subst a
    simp only [standardCircleSquareScalar_one, eq_self, or_true]
  have hlt : a < 1 := lt_of_le_of_ne ha.2 h1
  have hu : (a+1)/2 ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith [ha.1], by linarith⟩
  rw [standardCircleSquareScalar, AddCircle.coe_eq_zero_iff_of_mem_Ico hu]
  constructor
  · intro h
    left
    linarith
  · rintro (h | h)
    · rw [h]
      norm_num
    · exact (h1 h).elim

/-- The exact scalar kernel consists of equality and the two endpoint identifications. -/
theorem standardCircleSquareScalar_eq_iff {a b : ℝ}
    (ha : a ∈ Set.Icc (-1 : ℝ) 1) (hb : b ∈ Set.Icc (-1 : ℝ) 1) :
    standardCircleSquareScalar a = standardCircleSquareScalar b ↔
      a = b ∨ (a = -1 ∧ b = 1) ∨ (a = 1 ∧ b = -1) := by
  constructor
  · intro h
    by_cases ha1 : a = 1
    · have hb0 : standardCircleSquareScalar b = 0 := by
        rw [← h, ha1, standardCircleSquareScalar_one]
      rcases (standardCircleSquareScalar_eq_zero_iff hb).mp hb0 with hb1 | hb1
      · exact Or.inr (Or.inr ⟨ha1, hb1⟩)
      · exact Or.inl (ha1.trans hb1.symm)
    by_cases hb1 : b = 1
    · have ha0 : standardCircleSquareScalar a = 0 := by
        rw [h, hb1, standardCircleSquareScalar_one]
      rcases (standardCircleSquareScalar_eq_zero_iff ha).mp ha0 with ha0 | ha0
      · exact Or.inr (Or.inl ⟨ha0, hb1⟩)
      · exact Or.inl (ha0.trans hb1.symm)
    have hla : a < 1 := lt_of_le_of_ne ha.2 ha1
    have hlb : b < 1 := lt_of_le_of_ne hb.2 hb1
    have hua : (a+1)/2 ∈ Set.Ico (0 : ℝ) (0+1) :=
      ⟨by linarith [ha.1], by linarith⟩
    have hub : (b+1)/2 ∈ Set.Ico (0 : ℝ) (0+1) :=
      ⟨by linarith [hb.1], by linarith⟩
    have hu := (AddCircle.coe_eq_coe_iff_of_mem_Ico hua hub).mp h
    exact Or.inl (by linarith)
  · rintro (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [h]
    · rw [standardCircleSquareScalar_neg_one, standardCircleSquareScalar_one]
    · rw [standardCircleSquareScalar_neg_one, standardCircleSquareScalar_one]

end Markov
