import Markov.FareyHolonomy

/-! Coverage of the nonnegative determinant-one sector by the concrete Farey
matrix construction. The proof descends by subtraction on the coordinate mass;
it does not assume a Farey-tree coverage theorem or a geometric correspondence. -/

namespace Markov

/-- Nonnegative unimodular pairs are coordinatewise comparable, apart from
 the initial coordinate-axis pair. -/
theorem nonnegative_unimodular_descent (u v : ℤ × ℤ)
    (hu1 : 0 ≤ u.1) (hu2 : 0 ≤ u.2) (hv1 : 0 ≤ v.1) (hv2 : 0 ≤ v.2)
    (hdet : intDet u v = 1) :
    (u = (1, 0) ∧ v = (0, 1)) ∨
      (u.1 ≤ v.1 ∧ u.2 ≤ v.2) ∨ (v.1 ≤ u.1 ∧ v.2 ≤ u.2) := by
  by_cases huv : u.1 ≤ v.1 ∧ u.2 ≤ v.2
  · exact Or.inr (Or.inl huv)
  by_cases hvu : v.1 ≤ u.1 ∧ v.2 ≤ u.2
  · exact Or.inr (Or.inr hvu)
  apply Or.inl
  dsimp [intDet] at hdet
  by_cases hx : u.1 ≤ v.1
  · have hy : v.2 ≤ u.2 := by omega
    have hm1 := mul_nonneg (show 0 ≤ v.1 - u.1 by omega) hv2
    have hm2 := mul_nonneg hv1 (show 0 ≤ u.2 - v.2 by omega)
    nlinarith
  · have hy : u.2 < v.2 := by omega
    have hd1 : 0 ≤ u.1 - v.1 - 1 := by omega
    have hd2 : 0 ≤ v.2 - u.2 - 1 := by omega
    have hm1 := mul_nonneg hv1 hd2
    have hm2 := mul_nonneg hu2 hd1
    have hm3 := mul_nonneg hd1 hd2
    have hbound : u.1 + v.2 ≤ 2 := by nlinarith
    have hcoords : u.1 = 1 ∧ u.2 = 0 ∧ v.1 = 0 ∧ v.2 = 1 := by omega
    exact ⟨Prod.ext hcoords.1 hcoords.2.1, Prod.ext hcoords.2.2.1 hcoords.2.2.2⟩

/-- Coordinate mass used in the subtraction descent. -/
def fareyMass (u v : ℤ × ℤ) : ℕ := (u.1 + u.2 + v.1 + v.2).toNat

/-- Every nonnegative unimodular pair occurs as labels of actual integer
matrix words in the Farey construction. -/
theorem exists_fareyHolonomy_of_nonnegative (u v : ℤ × ℤ)
    (hu1 : 0 ≤ u.1) (hu2 : 0 ≤ u.2) (hv1 : 0 ≤ v.1) (hv2 : 0 ≤ v.2)
    (hdet : intDet u v = 1) : ∃ M N, FareyHolonomy u v M N := by
  generalize hm : fareyMass u v = n
  induction n using Nat.strong_induction_on generalizing u v with
  | h n ih =>
    have hsu : 0 < u.1 + u.2 := by
      by_contra hn
      have hz1 : u.1 = 0 := by omega
      have hz2 : u.2 = 0 := by omega
      simp [intDet, hz1, hz2] at hdet
    have hsv : 0 < v.1 + v.2 := by
      by_contra hn
      have hz1 : v.1 = 0 := by omega
      have hz2 : v.2 = 0 := by omega
      simp [intDet, hz1, hz2] at hdet
    rcases nonnegative_unimodular_descent u v hu1 hu2 hv1 hv2 hdet with hs | huv | hvu
    · rcases hs with ⟨rfl, rfl⟩
      exact ⟨modularGeneratorA, modularGeneratorB, FareyHolonomy.seed⟩
    · have hdet' : intDet u (v - u) = 1 := by
        simp only [intDet, Prod.fst_sub, Prod.snd_sub] at *
        nlinarith
      have hmass : fareyMass u (v - u) < n := by
        dsimp [fareyMass] at *
        omega
      obtain ⟨M, N, h⟩ := ih _ hmass u (v - u) hu1 hu2 (by exact sub_nonneg.mpr huv.1)
        (by exact sub_nonneg.mpr huv.2) hdet' rfl
      exact ⟨M, M * N, by simpa using h.left⟩
    · have hdet' : intDet (u - v) v = 1 := by
        simp only [intDet, Prod.fst_sub, Prod.snd_sub] at *
        nlinarith
      have hmass : fareyMass (u - v) v < n := by
        dsimp [fareyMass] at *
        omega
      obtain ⟨M, N, h⟩ := ih _ hmass (u - v) v (by exact sub_nonneg.mpr hvu.1)
        (by exact sub_nonneg.mpr hvu.2) hv1 hv2 hdet' rfl
      exact ⟨M * N, N, by simpa using h.right⟩

/-- Every direction label of the concrete construction is nonnegative. -/
theorem FareyHolonomy.nonnegative_labels {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) : 0 ≤ u.1 ∧ 0 ≤ u.2 ∧ 0 ≤ v.1 ∧ 0 ≤ v.2 := by
  induction h with
  | seed => norm_num
  | left _ ih =>
    rcases ih with ⟨hu1, hu2, hv1, hv2⟩
    exact ⟨hu1, hu2, add_nonneg hu1 hv1, add_nonneg hu2 hv2⟩
  | right _ ih =>
    rcases ih with ⟨hu1, hu2, hv1, hv2⟩
    exact ⟨add_nonneg hu1 hv1, add_nonneg hu2 hv2, hv1, hv2⟩

/-- Exact characterization of the direction pairs covered by this sector. -/
theorem exists_fareyHolonomy_iff (u v : ℤ × ℤ) :
    (∃ M N, FareyHolonomy u v M N) ↔
      0 ≤ u.1 ∧ 0 ≤ u.2 ∧ 0 ≤ v.1 ∧ 0 ≤ v.2 ∧ intDet u v = 1 := by
  constructor
  · rintro ⟨M, N, h⟩
    rcases h.nonnegative_labels with ⟨hu1, hu2, hv1, hv2⟩
    exact ⟨hu1, hu2, hv1, hv2, h.det_eq_one⟩
  · rintro ⟨hu1, hu2, hv1, hv2, hd⟩
    exact exists_fareyHolonomy_of_nonnegative u v hu1 hu2 hv1 hv2 hd

end Markov
