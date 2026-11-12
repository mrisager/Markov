import Markov.QuadraticField

/-! The coefficients `A₊, A₋` of Proposition 4 in a quadratic
extension, parametrized by the three integer holonomy traces `t,b,c`. -/

attribute [-instance] DivisionRing.toRatAlgebra
open scoped QuadraticAlgebra

namespace Markov

def traceCoefficient (t b c : ℤ) : TraceField t :=
  ⟨(((t : ℚ) ^ 2 - 2) * b - t * c) / ((t : ℚ) ^ 2 - 4),
    (2 * c - t * b) / ((t : ℚ) ^ 2 - 4)⟩

theorem traceDiscriminant_pos (t : ℤ) (ht : 3 ≤ t) :
    0 < (t : ℚ) ^ 2 - 4 := by
  have ht' : (3 : ℚ) ≤ t := by exact_mod_cast ht
  nlinarith

theorem traceCoefficient_mul_denominator (t b c : ℤ) (ht : 3 ≤ t) :
    traceCoefficient t b c * (traceRoot t - star (traceRoot t)) =
      (c : TraceField t) - star (traceRoot t) * (b : TraceField t) := by
  have hd := (traceDiscriminant_pos t ht).ne'
  ext <;> simp [traceCoefficient, traceRoot] <;> field_simp [hd] <;> ring

theorem traceRoot_sub_star_ne_zero (t : ℤ) :
    traceRoot t - star (traceRoot t) ≠ 0 := by
  intro h
  have hi := congrArg QuadraticAlgebra.im h
  norm_num [traceRoot] at hi

/-- The coefficient is exactly the quotient in the paper's definition of `A₊`. -/
theorem traceCoefficient_eq (t b c : ℤ) [ht : Fact (3 ≤ t)] :
    traceCoefficient t b c =
      ((c : TraceField t) - (traceRoot t)⁻¹ * b) /
        (traceRoot t - (traceRoot t)⁻¹) := by
  rw [← traceRoot_star_eq_inv]
  exact (eq_div_iff (traceRoot_sub_star_ne_zero t)).mpr
    (traceCoefficient_mul_denominator t b c ht.out)

/-- Conjugation exchanges the two coefficients of the paper. -/
theorem traceCoefficient_star (t b c : ℤ) (ht : 3 ≤ t) :
    star (traceCoefficient t b c) = traceCoefficient t b (t * b - c) := by
  have hd := (traceDiscriminant_pos t ht).ne'
  ext <;> simp [traceCoefficient] <;> field_simp [hd] <;> ring

theorem traceCoefficient_add_star (t b c : ℤ) (ht : 3 ≤ t) :
    traceCoefficient t b c + star (traceCoefficient t b c) = (b : TraceField t) := by
  have hd := (traceDiscriminant_pos t ht).ne'
  ext <;> simp [traceCoefficient]
  field_simp [hd]
  ring

/-- The usual field trace, calculated from left multiplication in the basis `(1,r)`. -/
theorem traceField_trace_eq (t : ℤ) (z : TraceField t) :
    Algebra.trace ℚ (TraceField t) z = 2 * z.re + (t : ℚ) * z.im := by
  let B := QuadraticAlgebra.basis (-1 : ℚ) (t : ℚ)
  have hb0 : B 0 = (1 : TraceField t) := by
    apply B.repr.injective
    ext i
    fin_cases i <;> simp [B, QuadraticAlgebra.basis_repr_apply]
  have hb1 : B 1 = traceRoot t := by
    apply B.repr.injective
    ext i
    fin_cases i <;> simp [B, QuadraticAlgebra.basis_repr_apply, traceRoot]
  rw [Algebra.trace_eq_matrix_trace B]
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Algebra.leftMulMatrix_eq_repr_mul,
    hb0, hb1, mul_one]
  simp [B, traceRoot]
  ring

/-- Proposition 4(iii) for the actual field trace, rather than just a formal sum. -/
theorem traceCoefficient_field_trace (t b c : ℤ) (ht : 3 ≤ t) :
    Algebra.trace ℚ (TraceField t) (traceCoefficient t b c) = (b : ℚ) := by
  rw [traceField_trace_eq]
  have hd := (traceDiscriminant_pos t ht).ne'
  dsimp [traceCoefficient]
  field_simp [hd]
  ring

/-- Proposition 4(ii), using the genuine algebra norm. -/
theorem traceCoefficient_field_norm (t b c : ℤ) (ht : 3 ≤ t)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) :
    Algebra.norm ℚ (traceCoefficient t b c) = (t : ℚ) ^ 2 / ((t : ℚ) ^ 2 - 4) := by
  have hd := (traceDiscriminant_pos t ht).ne'
  have hfq : (t : ℚ) ^ 2 + (b : ℚ) ^ 2 + (c : ℚ) ^ 2 = (t : ℚ) * b * c := by
    exact_mod_cast hf
  rw [traceField_norm_eq, QuadraticAlgebra.norm_def]
  dsimp [traceCoefficient]
  field_simp [hd]
  linear_combination -((t : ℚ) ^ 2 - 4) * hfq

theorem traceCoefficient_field_norm_gt_one (t b c : ℤ) (ht : 3 ≤ t)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) :
    1 < Algebra.norm ℚ (traceCoefficient t b c) := by
  rw [traceCoefficient_field_norm t b c ht hf]
  apply (lt_div_iff₀ (traceDiscriminant_pos t ht)).mpr
  linarith

/-- Clearing the paper's discriminant yields an integer linear combination of
`1` and the integral unit `r`. This also gives a short integrality proof. -/
theorem scaled_traceCoefficient (t b c : ℤ) (ht : 3 ≤ t) :
    ((t ^ 2 - 4 : ℤ) : TraceField t) * traceCoefficient t b c =
      (((t ^ 2 - 2) * b - t * c : ℤ) : TraceField t) +
        ((2 * c - t * b : ℤ) : TraceField t) * traceRoot t := by
  have hd := (traceDiscriminant_pos t ht).ne'
  ext <;> simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
    QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast,
    traceCoefficient, traceRoot, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im]
    <;> push_cast <;> field_simp [hd] <;> ring

theorem scaled_traceCoefficient_isIntegral (t b c : ℤ) (ht : 3 ≤ t) :
    IsIntegral ℤ (((t ^ 2 - 4 : ℤ) : TraceField t) * traceCoefficient t b c) := by
  rw [scaled_traceCoefficient t b c ht]
  exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul (traceRoot_isIntegral t))

/-- The product relation after clearing the discriminant. -/
theorem traceCoefficient_scaled_product (t b c : ℤ) (ht : 3 ≤ t)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) :
    ((t ^ 2 - 4 : ℤ) : TraceField t) *
      (traceCoefficient t b c * star (traceCoefficient t b c)) = (t : TraceField t) ^ 2 := by
  rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, ← traceField_norm_eq,
    traceCoefficient_field_norm t b c ht hf]
  have hd := (traceDiscriminant_pos t ht).ne'
  have hq : ((t : ℚ) ^ 2 - 4) * ((t : ℚ) ^ 2 / ((t : ℚ) ^ 2 - 4)) = (t : ℚ) ^ 2 := by
    field_simp
  have hm := congrArg (algebraMap ℚ (TraceField t)) hq
  simpa using hm

/-- The exact monic-polynomial calculation from Proposition 4(iv). -/
theorem scaled_traceCoefficient_equation (t b c : ℤ) (ht : 3 ≤ t)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) :
    let z := ((t ^ 2 - 4 : ℤ) : TraceField t) * traceCoefficient t b c
    z ^ 2 - (((t ^ 2 - 4) * b : ℤ) : TraceField t) * z +
      (((t ^ 2 - 4) * t ^ 2 : ℤ) : TraceField t) = 0 := by
  have hs := traceCoefficient_add_star t b c ht
  have hp := traceCoefficient_scaled_product t b c ht hf
  dsimp
  push_cast
  rw [← hs]
  calc
    _ = ((t : TraceField t) ^ 2 - 4) *
      ((t : TraceField t) ^ 2 - ((t : TraceField t) ^ 2 - 4) *
        (traceCoefficient t b c * star (traceCoefficient t b c))) := by ring
    _ = 0 := by push_cast at hp; rw [hp]; ring

/-- Integrality by the paper's monic polynomial proof. -/
theorem scaled_traceCoefficient_isIntegral_via_polynomial (t b c : ℤ) (ht : 3 ≤ t)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) :
    IsIntegral ℤ (((t ^ 2 - 4 : ℤ) : TraceField t) * traceCoefficient t b c) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C ((t ^ 2 - 4) * b) * Polynomial.X +
    Polynomial.C ((t ^ 2 - 4) * t ^ 2), ?_, ?_⟩
  · monicity!
  · simpa only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
      using scaled_traceCoefficient_equation t b c ht hf

end Markov
