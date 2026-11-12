import T1BoundaryOrbits

/-! The twelve actual strict-sector images are pairwise disjoint, and
avoid both finite boundary orbits. This is integral coordinate geometry. -/
namespace Markov

private theorem t1_action0_unique (j : Fin 6) (b c : Bool) (p q : ℤ × ℤ)
    (hp : 0 < p.2 ∧ 2*p.2 < p.1) (hq : 0 < q.2 ∧ 2*q.2 < q.1)
    (he : t1_dihedralAction 0 b p = t1_dihedralAction j c q) :
    (0 : Fin 6) = j ∧ b = c ∧ p = q := by
  fin_cases j <;> cases b <;> cases c <;>
    simp_all [t1_dihedralAction,t1_latticeTurn,t1_latticeSwap,Prod.ext_iff] <;> omega

private theorem t1_action1_unique (j : Fin 6) (b c : Bool) (p q : ℤ × ℤ)
    (hp : 0 < p.2 ∧ 2*p.2 < p.1) (hq : 0 < q.2 ∧ 2*q.2 < q.1)
    (he : t1_dihedralAction 1 b p = t1_dihedralAction j c q) :
    (1 : Fin 6) = j ∧ b = c ∧ p = q := by
  fin_cases j <;> cases b <;> cases c <;>
    simp_all [t1_dihedralAction,t1_latticeTurn,t1_latticeSwap,Prod.ext_iff] <;> omega

private theorem t1_action2_unique (j : Fin 6) (b c : Bool) (p q : ℤ × ℤ)
    (hp : 0 < p.2 ∧ 2*p.2 < p.1) (hq : 0 < q.2 ∧ 2*q.2 < q.1)
    (he : t1_dihedralAction 2 b p = t1_dihedralAction j c q) :
    (2 : Fin 6) = j ∧ b = c ∧ p = q := by
  fin_cases j <;> cases b <;> cases c <;>
    simp_all [t1_dihedralAction,t1_latticeTurn,t1_latticeSwap,Prod.ext_iff] <;> omega

private theorem t1_action3_unique (j : Fin 6) (b c : Bool) (p q : ℤ × ℤ)
    (hp : 0 < p.2 ∧ 2*p.2 < p.1) (hq : 0 < q.2 ∧ 2*q.2 < q.1)
    (he : t1_dihedralAction 3 b p = t1_dihedralAction j c q) :
    (3 : Fin 6) = j ∧ b = c ∧ p = q := by
  fin_cases j <;> cases b <;> cases c <;>
    simp_all [t1_dihedralAction,t1_latticeTurn,t1_latticeSwap,Prod.ext_iff] <;> omega

private theorem t1_action4_unique (j : Fin 6) (b c : Bool) (p q : ℤ × ℤ)
    (hp : 0 < p.2 ∧ 2*p.2 < p.1) (hq : 0 < q.2 ∧ 2*q.2 < q.1)
    (he : t1_dihedralAction 4 b p = t1_dihedralAction j c q) :
    (4 : Fin 6) = j ∧ b = c ∧ p = q := by
  fin_cases j <;> cases b <;> cases c <;>
    simp_all [t1_dihedralAction,t1_latticeTurn,t1_latticeSwap,Prod.ext_iff] <;> omega

private theorem t1_action5_unique (j : Fin 6) (b c : Bool) (p q : ℤ × ℤ)
    (hp : 0 < p.2 ∧ 2*p.2 < p.1) (hq : 0 < q.2 ∧ 2*q.2 < q.1)
    (he : t1_dihedralAction 5 b p = t1_dihedralAction j c q) :
    (5 : Fin 6) = j ∧ b = c ∧ p = q := by
  fin_cases j <;> cases b <;> cases c <;>
    simp_all [t1_dihedralAction,t1_latticeTurn,t1_latticeSwap,Prod.ext_iff] <;> omega

theorem t1_dihedralAction_strict_unique (k j : Fin 6) (b c : Bool) (p q : ℤ × ℤ)
    (hp : 0 < p.2 ∧ 2*p.2 < p.1) (hq : 0 < q.2 ∧ 2*q.2 < q.1)
    (he : t1_dihedralAction k b p = t1_dihedralAction j c q) :
    k = j ∧ b = c ∧ p = q := by
  fin_cases k
  · exact t1_action0_unique j b c p q hp hq he
  · exact t1_action1_unique j b c p q hp hq he
  · exact t1_action2_unique j b c p q hp hq he
  · exact t1_action3_unique j b c p q hp hq he
  · exact t1_action4_unique j b c p q hp hq he
  · exact t1_action5_unique j b c p q hp hq he

theorem t1_dihedralAction_strict_not_boundary (k : Fin 6) (b : Bool) (p : ℤ × ℤ)
    (hp : 0 < p.2 ∧ 2*p.2 < p.1) :
    t1_dihedralAction k b p ∉ t1_shortOrbit ∧ t1_dihedralAction k b p ∉ t1_middleOrbit := by
  fin_cases k <;> cases b <;>
    simp_all [t1_dihedralAction,t1_latticeTurn,t1_latticeSwap,
      t1_shortOrbit,t1_middleOrbit,Prod.ext_iff] <;> omega

end Markov
