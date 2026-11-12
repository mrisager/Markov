import T1LatticeTurns
import T1GeometricRotation
import T1GeometricReflection

/-! The twelve explicit operations preserve the actual primitive geometric
length. Their formulas and primitiveness are independently proved. -/
noncomputable section
namespace Markov

theorem t1_geometricLength_rotation_iterate (n : ℕ) (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    t1_geometricLength ((t1_latticeRotation^[n]) p) = t1_geometricLength p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',t1_geometricLength_rotation _
      ((t1_latticeRotation_iterate_coprime_iff n p).mpr hp),ih]

theorem t1_geometricLength_turn (k : Fin 6) (p : ℤ × ℤ) (hp : IsCoprime p.1 p.2) :
    t1_geometricLength (t1_latticeTurn k p) = t1_geometricLength p := by
  rw [t1_latticeTurn_eq_iterate]
  exact t1_geometricLength_rotation_iterate k.val p hp

theorem t1_geometricLength_dihedralAction (k : Fin 6) (b : Bool) (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    t1_geometricLength (t1_dihedralAction k b p) = t1_geometricLength p := by
  unfold t1_dihedralAction
  cases b
  · exact t1_geometricLength_turn k p hp
  · exact (t1_geometricLength_turn k (t1_latticeSwap p) hp.symm).trans
      (t1_geometricLength_swap p hp)

end Markov
