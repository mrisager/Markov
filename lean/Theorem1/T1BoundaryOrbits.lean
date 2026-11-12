import T1LatticeTurns

/-! The two actual exceptional primitive lattice orbits. Their members,
cardinalities, and disjointness are finite integer facts checked by the kernel. -/
namespace Markov

def t1_shortOrbit : Finset (ℤ × ℤ) :=
  {(1,0),(1,1),(0,1),(-1,0),(-1,-1),(0,-1)}

def t1_middleOrbit : Finset (ℤ × ℤ) :=
  {(2,1),(1,2),(-1,1),(-2,-1),(-1,-2),(1,-1)}

theorem t1_shortOrbit_card : t1_shortOrbit.card = 6 := by decide

theorem t1_middleOrbit_card : t1_middleOrbit.card = 6 := by decide

theorem t1_boundaryOrbits_disjoint : Disjoint t1_shortOrbit t1_middleOrbit := by decide

theorem t1_shortOrbit_eq_turn_image : t1_shortOrbit =
    Finset.univ.image (fun k : Fin 6 => t1_latticeTurn k (1,0)) := by decide

theorem t1_middleOrbit_eq_turn_image : t1_middleOrbit =
    Finset.univ.image (fun k : Fin 6 => t1_latticeTurn k (2,1)) := by decide

theorem t1_shortOrbit_neg_iff (p : ℤ × ℤ) : -p ∈ t1_shortOrbit ↔ p ∈ t1_shortOrbit := by
  rcases p with ⟨x,y⟩
  simp [t1_shortOrbit,Prod.ext_iff]
  omega

theorem t1_middleOrbit_neg_iff (p : ℤ × ℤ) : -p ∈ t1_middleOrbit ↔ p ∈ t1_middleOrbit := by
  rcases p with ⟨x,y⟩
  simp [t1_middleOrbit,Prod.ext_iff]
  omega

theorem t1_positive_coprime_multiple_self (a n : ℤ) (hn : 0 < n)
    (hp : IsCoprime (a*n) n) : n = 1 := by
  obtain ⟨x,y,hxy⟩ := hp
  have he : n*(a*x+y) = 1 := by linear_combination hxy
  rcases Int.eq_one_or_neg_one_of_mul_eq_one he with h | h
  · exact h
  · omega

end Markov
