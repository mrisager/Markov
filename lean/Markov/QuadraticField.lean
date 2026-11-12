import Markov.TraceAlgebra
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Trace.Defs

/-! The actual quadratic field in Proposition 4. We use the basis `(1,r)`
with `r² - t*r + 1 = 0`, instead of the basis `(1,√(t²-4))`.
Both describe the same quadratic extension; the real embedding will select
the larger root. No geometric trace is postulated in this module. -/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped QuadraticAlgebra

namespace Markov

theorem discriminant_not_square (t : ℤ) (ht : 3 ≤ t) : ¬IsSquare (t ^ 2 - 4) := by
  rintro ⟨s, hs⟩
  have hs' : |s| ^ 2 = t ^ 2 - 4 := by nlinarith [sq_abs s]
  have hlt : |s| < t := by
    by_contra h
    have hm := mul_nonneg (sub_nonneg.mpr (le_of_not_gt h))
      (show 0 ≤ |s| + t by have := abs_nonneg s; omega)
    nlinarith
  have hle : |s| ≤ t - 1 := by omega
  have hm := mul_nonneg (sub_nonneg.mpr hle)
    (show 0 ≤ t - 1 + |s| by have := abs_nonneg s; omega)
  nlinarith

/-- The polynomial `X² - tX + 1` has no rational root for an integer `t ≥ 3`. -/
theorem trace_polynomial_no_rat_root (t : ℤ) (ht : 3 ≤ t) (q : ℚ) :
    q ^ 2 ≠ -1 + (t : ℚ) * q := by
  intro hq
  have hn : ¬IsSquare ((t ^ 2 - 4 : ℤ) : ℚ) :=
    Rat.isSquare_intCast_iff.not.mpr (discriminant_not_square t ht)
  apply hn
  refine ⟨2 * q - t, ?_⟩
  push_cast
  nlinarith

abbrev TraceField (t : ℤ) := QuadraticAlgebra ℚ (-1) (t : ℚ)

instance traceFieldIrreducible (t : ℤ) [ht : Fact (3 ≤ t)] :
    Fact (∀ q : ℚ, q ^ 2 ≠ -1 + (t : ℚ) * q) :=
  ⟨trace_polynomial_no_rat_root t ht.out⟩

noncomputable instance traceFieldNumberField (t : ℤ) [Fact (3 ≤ t)] :
    NumberField (TraceField t) where
  to_charZero := inferInstance
  to_finiteDimensional := by
    have ha : (DivisionRing.toRatAlgebra : Algebra ℚ (TraceField t)) =
        (inferInstance : Algebra ℚ (TraceField t)) := Subsingleton.elim _ _
    change @Module.Finite ℚ (TraceField t) _ _ (DivisionRing.toRatAlgebra.toModule)
    rw [ha]
    infer_instance

theorem traceField_finrank (t : ℤ) : Module.finrank ℚ (TraceField t) = 2 :=
  QuadraticAlgebra.finrank_eq_two _ _

/-- The distinguished root, which the positive real embedding sends to
`(t + sqrt(t²-4))/2`. -/
def traceRoot (t : ℤ) : TraceField t := QuadraticAlgebra.omega

theorem traceRoot_equation (t : ℤ) :
    traceRoot t ^ 2 - (t : TraceField t) * traceRoot t + 1 = 0 := by
  ext <;> simp [traceRoot, pow_two]

theorem traceRoot_star_mul (t : ℤ) : traceRoot t * star (traceRoot t) = 1 := by
  ext <;> simp [traceRoot]

theorem traceRoot_norm (t : ℤ) : QuadraticAlgebra.norm (traceRoot t) = 1 := by
  simp [traceRoot, QuadraticAlgebra.norm_def]

/-- Identify the library's explicit quadratic norm with the genuine algebra norm. -/
theorem traceField_norm_eq (t : ℤ) (z : TraceField t) :
    Algebra.norm ℚ z = QuadraticAlgebra.norm z := by
  rw [Algebra.norm_apply]
  exact QuadraticAlgebra.det_toLinearMap_eq_norm z

theorem traceRoot_field_norm (t : ℤ) : Algebra.norm ℚ (traceRoot t) = 1 := by
  rw [traceField_norm_eq, traceRoot_norm]

theorem traceRoot_star_eq_inv (t : ℤ) [Fact (3 ≤ t)] :
    star (traceRoot t) = (traceRoot t)⁻¹ := by
  exact eq_inv_of_mul_eq_one_right (traceRoot_star_mul t)

/-- Integrality from the monic polynomial used in the paper. -/
theorem traceRoot_isIntegral (t : ℤ) : IsIntegral ℤ (traceRoot t) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1, ?_, ?_⟩
  · monicity!
  · simpa only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C,
      Polynomial.eval₂_one] using traceRoot_equation t

theorem traceRoot_star_isIntegral (t : ℤ) : IsIntegral ℤ (star (traceRoot t)) := by
  have heq : star (traceRoot t) = (t : TraceField t) - traceRoot t := by
    ext <;> simp [traceRoot]
  rw [heq]
  exact (isIntegral_algebraMap (R := ℤ)).sub (traceRoot_isIntegral t)

/-- Proposition 4(i): the root is a unit in the ring of algebraic integers. -/
theorem traceRoot_isUnit_integerRing (t : ℤ) :
    IsUnit (⟨traceRoot t, traceRoot_isIntegral t⟩ : integralClosure ℤ (TraceField t)) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨star (traceRoot t), traceRoot_star_isIntegral t⟩, ?_⟩
  apply Subtype.ext
  exact traceRoot_star_mul t

end Markov
