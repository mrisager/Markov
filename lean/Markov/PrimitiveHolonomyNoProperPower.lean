import Mathlib
import Markov.PaperPrimitiveHolonomy
import Markov.PrimitiveRationalDensity

noncomputable section
namespace Markov

/-- A primitive integral vector has no natural scalar factor except one. -/
theorem primitiveDirection_nat_smul_eq_one {p q : ℤ × ℤ} (hp : IsCoprime p.1 p.2)
    {n : ℕ} (he : p = n • q) : n = 1 := by
  have h1 : p.1 = (n : ℤ) * q.1 := by
    simpa [nsmul_eq_mul] using congrArg Prod.fst he
  have h2 : p.2 = (n : ℤ) * q.2 := by
    simpa [nsmul_eq_mul] using congrArg Prod.snd he
  have hu : IsUnit (n : ℤ) := hp.isUnit_of_dvd' ⟨q.1, h1⟩ ⟨q.2, h2⟩
  simpa using Int.isUnit_iff_natAbs_eq.mp hu

/-- The same fact applies in every signed quadrant of the canonical construction. -/
theorem quadrantPrimitiveDirection_nat_smul_eq_one (k : Fin 4) {p q : ℤ × ℤ}
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p)) {n : ℕ}
    (he : p = n • q) : n = 1 :=
  primitiveDirection_nat_smul_eq_one ((quadrantCoordinates_coprime_iff k p).mp hp.2.2) he

/-- Taking abelianization of an actual positive power gives its natural scalar multiple. -/
theorem paperTraceAbelianizationCoordinates_pow_toAdd (g : modularTraceSubgroup) (n : ℕ) :
    (paperTraceAbelianizationCoordinates (g ^ n)).toAdd =
      n • (paperTraceAbelianizationCoordinates g).toAdd := by
  rw [map_pow]
  rfl

/-- The canonical actual primitive holonomy cannot be a proper natural power in the deck group. -/
theorem paperPrimitiveHolonomy_pow_eq_one (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p))
    (g : modularTraceSubgroup) (n : ℕ)
    (he : paperPrimitiveHolonomy k p hp = g ^ n) : n = 1 := by
  have hc := congrArg (fun h : modularTraceSubgroup =>
    (paperTraceAbelianizationCoordinates h).toAdd) he
  dsimp only at hc
  rw [paperPrimitiveHolonomy_coordinates, paperTraceAbelianizationCoordinates_pow_toAdd] at hc
  exact quadrantPrimitiveDirection_nat_smul_eq_one k hp hc

/-- In particular, no exponent strictly greater than one can yield the canonical holonomy. -/
theorem paperPrimitiveHolonomy_not_proper_pow (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p))
    (g : modularTraceSubgroup) (n : ℕ) (hn : 1 < n) :
    paperPrimitiveHolonomy k p hp ≠ g ^ n := by
  intro he
  have h1 := paperPrimitiveHolonomy_pow_eq_one k p hp g n he
  omega

end Markov

