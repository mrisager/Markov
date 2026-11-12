import T1FareyWords

/-! Every actual primitive direction strictly between (1,0) and (2,1)
is the mediant born at one of the literal finite Farey words. -/
namespace Markov

theorem t1_strict_sector_coordinate_primitive (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) : IsCoprime (p.1-2*p.2) p.2 := by
  obtain ⟨a,b,hab⟩ := hp
  refine ⟨a,2*a+b,?_⟩
  linear_combination hab

theorem t1_strict_sector_exists_farey_word (p : ℤ × ℤ)
    (hp2 : 0 < p.2) (hp12 : 2*p.2 < p.1) (hp : IsCoprime p.1 p.2) :
    ∃ w : List Bool, t1_fareyWordDirection w = p := by
  let c : ℤ × ℤ := (p.1-2*p.2,p.2)
  have hc1 : 0 ≤ c.1 := by dsimp [c]; omega
  have hc2 : 0 ≤ c.2 := hp2.le
  have hcop : IsCoprime c.1 c.2 := t1_strict_sector_coordinate_primitive p hp
  obtain ⟨u,v,hu1,hu2,hv1,hv2,hd,hpval⟩ :=
    nonnegative_primitive_in_unimodular_pair c hc1 hc2 hcop
  obtain ⟨M,N,h⟩ := exists_seededFarey_of_nonnegative_coordinates
    (1,0) (2,1) u v modularGeneratorA (modularGeneratorA * (modularGeneratorA * modularGeneratorB))
      hu1 hu2 hv1 hv2 hd
  have hcp : seededDirection (1,0) (2,1) c = p := by
    apply Prod.ext
    · simp [seededDirection,c]
      ring
    · simp [seededDirection,c]
  have hpv : p = seededDirection (1,0) (2,1) u ∨
      p = seededDirection (1,0) (2,1) v := by
    rcases hpval with hc | hc
    · left; rw [← hc]; exact hcp.symm
    · right; rw [← hc]; exact hcp.symm
  have hlabel : p = (1,0) ∨ p = (2,1) ∨
      ∃ a b P Q, SeededFarey (1,0) (2,1) modularGeneratorA
        (modularGeneratorA * (modularGeneratorA * modularGeneratorB)) a b P Q ∧ p = a+b := by
    rcases hpv with rfl | rfl
    · exact h.labels_seed_or_birth.1
    · exact h.labels_seed_or_birth.2
  rcases hlabel with haxis | haxis | ⟨a,b,P,Q,hab,hpab⟩
  · rw [haxis] at hp2; norm_num at hp2
  · rw [haxis] at hp12; norm_num at hp12
  · obtain ⟨w,hw,_⟩ := t1_seededFarey_exists_word hab
    refine ⟨w,?_⟩
    simp only [t1_fareyWordDirection,hw]
    exact hpab.symm

end Markov
