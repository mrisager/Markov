import T1LatticeRotationCoordinates
import T1ReflectionAlgebra

/-! The six literal integral turns, and the twelve lattice operations they
produce together with the proved coordinate reflection. -/
namespace Markov

def t1_latticeTurn : Fin 6 → (ℤ × ℤ) → (ℤ × ℤ)
  | 0,p => p
  | 1,p => (p.1-p.2,p.1)
  | 2,p => (-p.2,p.1-p.2)
  | 3,p => (-p.1,-p.2)
  | 4,p => (p.2-p.1,-p.1)
  | 5,p => (p.2,p.2-p.1)

def t1_dihedralAction (k : Fin 6) (b : Bool) (p : ℤ × ℤ) : ℤ × ℤ :=
  t1_latticeTurn k (if b then t1_latticeSwap p else p)

theorem t1_latticeRotation_coprime_iff (p : ℤ × ℤ) :
    IsCoprime (t1_latticeRotation p).1 (t1_latticeRotation p).2 ↔ IsCoprime p.1 p.2 := by
  constructor
  · rintro ⟨a,b,hab⟩
    refine ⟨a+b,-a,?_⟩
    dsimp [t1_latticeRotation] at hab
    linear_combination hab
  · exact t1_latticeRotation_coprime p

theorem t1_latticeRotation_iterate_coprime_iff (n : ℕ) (p : ℤ × ℤ) :
    IsCoprime ((t1_latticeRotation^[n]) p).1 ((t1_latticeRotation^[n]) p).2 ↔
      IsCoprime p.1 p.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',t1_latticeRotation_coprime_iff,ih]

theorem t1_latticeTurn_eq_iterate (k : Fin 6) (p : ℤ × ℤ) :
    t1_latticeTurn k p = (t1_latticeRotation^[k.val]) p := by
  fin_cases k <;> apply Prod.ext <;>
    simp [t1_latticeTurn,t1_latticeRotation,Function.iterate_succ_apply'] <;> ring

theorem t1_latticeTurn_coprime_iff (k : Fin 6) (p : ℤ × ℤ) :
    IsCoprime (t1_latticeTurn k p).1 (t1_latticeTurn k p).2 ↔ IsCoprime p.1 p.2 := by
  rw [t1_latticeTurn_eq_iterate]
  exact t1_latticeRotation_iterate_coprime_iff k.val p

theorem t1_dihedralAction_coprime_iff (k : Fin 6) (b : Bool) (p : ℤ × ℤ) :
    IsCoprime (t1_dihedralAction k b p).1 (t1_dihedralAction k b p).2 ↔ IsCoprime p.1 p.2 := by
  unfold t1_dihedralAction
  rw [t1_latticeTurn_coprime_iff]
  cases b
  · rfl
  · exact ⟨IsCoprime.symm,IsCoprime.symm⟩

def t1_oppositeTurn (k : Fin 6) : Fin 6 := ⟨(k.val+3)%6,Nat.mod_lt _ (by decide)⟩

theorem t1_latticeTurn_opposite (k : Fin 6) (p : ℤ × ℤ) :
    t1_latticeTurn (t1_oppositeTurn k) p = -t1_latticeTurn k p := by
  fin_cases k <;> apply Prod.ext <;>
    simp [t1_oppositeTurn,t1_latticeTurn]

theorem t1_dihedralAction_opposite (k : Fin 6) (b : Bool) (p : ℤ × ℤ) :
    t1_dihedralAction (t1_oppositeTurn k) b p = -t1_dihedralAction k b p :=
  t1_latticeTurn_opposite k (if b then t1_latticeSwap p else p)

end Markov
