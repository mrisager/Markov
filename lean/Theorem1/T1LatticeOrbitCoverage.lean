import T1BoundaryOrbits

/-! Actual finite sector coverage of every primitive signed integer vector.
The normal form is proved by integer inequalities and Bézout primitiveness. -/
namespace Markov

def t1_hasStrictDihedralForm (p : ℤ × ℤ) : Prop :=
  ∃ (k : Fin 6) (b : Bool) (q : ℤ × ℤ),
    0 < q.2 ∧ 2*q.2 < q.1 ∧ IsCoprime q.1 q.2 ∧ p = t1_dihedralAction k b q

private theorem t1_strict_form_of_image (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2)
    (k : Fin 6) (b : Bool) (q : ℤ × ℤ) (hq2 : 0 < q.2) (hq12 : 2*q.2 < q.1)
    (he : p = t1_dihedralAction k b q) : t1_hasStrictDihedralForm p := by
  refine ⟨k,b,q,hq2,hq12,?_,he⟩
  apply (t1_dihedralAction_coprime_iff k b q).mp
  rw [← he]
  exact hp

private theorem t1_upper_half_primitive_coverage (x y : ℤ) (hy : 0 < y)
    (hp : IsCoprime x y) :
    (x,y) ∈ t1_shortOrbit ∨ (x,y) ∈ t1_middleOrbit ∨ t1_hasStrictDihedralForm (x,y) := by
  by_cases hx : 0 < x
  · by_cases hyx : y < x
    · rcases lt_trichotomy (2*y) x with hlt | heq | hgt
      · exact Or.inr (Or.inr (t1_strict_form_of_image (x,y) hp 0 false (x,y) hy hlt rfl))
      · have hn : y = 1 := t1_positive_coprime_multiple_self 2 y hy (by rwa [← heq] at hp)
        have hx2 : x = 2 := by omega
        subst x; subst y
        exact Or.inr (Or.inl (by decide))
      · apply Or.inr; apply Or.inr
        apply t1_strict_form_of_image (x,y) hp 5 true (x,x-y) (by dsimp; omega) (by dsimp; omega)
        apply Prod.ext <;> simp [t1_dihedralAction,t1_latticeTurn,t1_latticeSwap]
    · by_cases hexy : y = x
      · have hn : x = 1 := t1_positive_coprime_multiple_self 1 x hx (by simpa [hexy] using hp)
        have hy1 : y = 1 := by omega
        subst x; subst y
        exact Or.inl (by decide)
      · have hxy : x < y := by omega
        rcases lt_trichotomy (2*x) y with hlt | heq | hgt
        · exact Or.inr (Or.inr (t1_strict_form_of_image (x,y) hp 0 true (y,x) hx hlt rfl))
        · have hn : x = 1 := t1_positive_coprime_multiple_self 2 x hx (by
            have hh := hp.symm
            rwa [← heq] at hh)
          have hy2 : y = 2 := by omega
          subst x; subst y
          exact Or.inr (Or.inl (by decide))
        · apply Or.inr; apply Or.inr
          apply t1_strict_form_of_image (x,y) hp 1 false (y,y-x) (by dsimp; omega) (by dsimp; omega)
          apply Prod.ext <;> simp [t1_dihedralAction,t1_latticeTurn]
  · by_cases hx0 : x = 0
    · subst x
      have hn : y = 1 := t1_positive_coprime_multiple_self 0 y hy (by simpa using hp)
      subst y
      exact Or.inl (by decide)
    · have hxneg : x < 0 := by omega
      rcases lt_trichotomy y (-x) with hlt | heq | hgt
      · apply Or.inr; apply Or.inr
        apply t1_strict_form_of_image (x,y) hp 1 true (y-x,y) hy (by dsimp; omega)
        apply Prod.ext <;> simp [t1_dihedralAction,t1_latticeTurn,t1_latticeSwap]
      · have hxy : x = -y := by omega
        have hn : y = 1 := t1_positive_coprime_multiple_self (-1) y hy (by simpa [hxy] using hp)
        have hx1 : x = -1 := by omega
        subst x; subst y
        exact Or.inr (Or.inl (by decide))
      · apply Or.inr; apply Or.inr
        apply t1_strict_form_of_image (x,y) hp 2 false (y-x,-x) (by dsimp; omega) (by dsimp; omega)
        apply Prod.ext <;> simp [t1_dihedralAction,t1_latticeTurn]

theorem t1_primitive_lattice_orbit_coverage (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    p ∈ t1_shortOrbit ∨ p ∈ t1_middleOrbit ∨ t1_hasStrictDihedralForm p := by
  rcases p with ⟨x,y⟩
  by_cases hy0 : y = 0
  · subst y
    obtain ⟨a,b,hab⟩ := hp
    have hx : x*a = 1 := by nlinarith [hab]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hx with rfl | rfl <;> exact Or.inl (by decide)
  · by_cases hy : 0 < y
    · exact t1_upper_half_primitive_coverage x y hy hp
    · have hyneg : 0 < -y := by omega
      rcases t1_upper_half_primitive_coverage (-x) (-y) hyneg hp.neg_neg with hs | hm | hi
      · exact Or.inl ((t1_shortOrbit_neg_iff (x,y)).mp hs)
      · exact Or.inr (Or.inl ((t1_middleOrbit_neg_iff (x,y)).mp hm))
      · obtain ⟨k,b,q,hq2,hq12,hcop,he⟩ := hi
        refine Or.inr (Or.inr ⟨t1_oppositeTurn k,b,q,hq2,hq12,hcop,?_⟩)
        have he' : (x,y) = -t1_dihedralAction k b q := by
          simpa using congrArg Neg.neg he
        exact he'.trans (t1_dihedralAction_opposite k b q).symm

end Markov
