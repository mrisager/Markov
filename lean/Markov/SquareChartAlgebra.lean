import Markov.PaperQuadrilateralInversion

noncomputable section
namespace Markov

/-- Positive denominator of the square chart. -/
theorem squareChart_den_pos (x y : ℝ) : 0 < x ^ 2 + y ^ 2 + 1 := by
  positivity

/-- The sum denominator is the reciprocal of the forward denominator. -/
theorem squareChart_forward_den (x y : ℝ) :
    2 - (x ^ 2 + y ^ 2 - 1 - 2*x) / (x ^ 2 + y ^ 2 + 1) -
      (x ^ 2 + y ^ 2 - 1 + 2*x) / (x ^ 2 + y ^ 2 + 1) =
        4 / (x ^ 2 + y ^ 2 + 1) := by
  have h := ne_of_gt (squareChart_den_pos x y)
  field_simp
  ring

/-- Exact positive radicand identity for the square chart. -/
theorem squareChart_forward_radicand (x y : ℝ) :
    4 - 2*((x ^ 2 + y ^ 2 - 1 - 2*x) / (x ^ 2 + y ^ 2 + 1))^2 -
      2*((x ^ 2 + y ^ 2 - 1 + 2*x) / (x ^ 2 + y ^ 2 + 1))^2 =
        (4*y / (x ^ 2 + y ^ 2 + 1))^2 := by
  have h := ne_of_gt (squareChart_den_pos x y)
  field_simp
  ring

/-- Recovery of the real coordinate from the chart. -/
theorem squareChart_forward_inverse_x (x y : ℝ) :
    (((x ^ 2 + y ^ 2 - 1 + 2*x) / (x ^ 2 + y ^ 2 + 1)) -
      ((x ^ 2 + y ^ 2 - 1 - 2*x) / (x ^ 2 + y ^ 2 + 1))) /
      (2 - (x ^ 2 + y ^ 2 - 1 - 2*x) / (x ^ 2 + y ^ 2 + 1) -
        (x ^ 2 + y ^ 2 - 1 + 2*x) / (x ^ 2 + y ^ 2 + 1)) = x := by
  rw [squareChart_forward_den]
  have h := ne_of_gt (squareChart_den_pos x y)
  field_simp
  ring

/-- Recovery of the height from the chart. -/
theorem squareChart_forward_inverse_y (x y : ℝ) (hy : 0 < y) :
    Real.sqrt (4 - 2*((x ^ 2 + y ^ 2 - 1 - 2*x) / (x ^ 2 + y ^ 2 + 1))^2 -
      2*((x ^ 2 + y ^ 2 - 1 + 2*x) / (x ^ 2 + y ^ 2 + 1))^2) /
      (2 - (x ^ 2 + y ^ 2 - 1 - 2*x) / (x ^ 2 + y ^ 2 + 1) -
        (x ^ 2 + y ^ 2 - 1 + 2*x) / (x ^ 2 + y ^ 2 + 1)) = y := by
  rw [squareChart_forward_radicand, squareChart_forward_den,
    Real.sqrt_sq (by positivity : 0 ≤ 4*y / (x ^ 2 + y ^ 2 + 1))]
  have h := ne_of_gt (squareChart_den_pos x y)
  field_simp

/-- Norm of the inverse chart. -/
theorem squareChart_inverse_norm (a b : ℝ) (hD : 2 - a - b ≠ 0)
    (hrad : 0 ≤ 4 - 2*a^2 - 2*b^2) :
    ((b-a) / (2-a-b))^2 + (Real.sqrt (4-2*a^2-2*b^2) / (2-a-b))^2 =
      (2+a+b) / (2-a-b) := by
  rw [div_pow, div_pow, Real.sq_sqrt hrad]
  field_simp
  ring

/-- First coordinate after applying the inverse chart. -/
theorem squareChart_inverse_forward_a (a b : ℝ) (hD : 2 - a - b ≠ 0)
    (hrad : 0 ≤ 4 - 2*a^2 - 2*b^2) :
    ((((b-a) / (2-a-b))^2 + (Real.sqrt (4-2*a^2-2*b^2) / (2-a-b))^2) - 1 -
      2*((b-a) / (2-a-b))) /
      ((((b-a) / (2-a-b))^2 + (Real.sqrt (4-2*a^2-2*b^2) / (2-a-b))^2) + 1) = a := by
  rw [squareChart_inverse_norm a b hD hrad]
  have hden : (2+a+b)/(2-a-b) + 1 = 4/(2-a-b) := by
    field_simp
    ring
  rw [hden]
  field_simp
  ring

/-- Second coordinate after applying the inverse chart. -/
theorem squareChart_inverse_forward_b (a b : ℝ) (hD : 2 - a - b ≠ 0)
    (hrad : 0 ≤ 4 - 2*a^2 - 2*b^2) :
    ((((b-a) / (2-a-b))^2 + (Real.sqrt (4-2*a^2-2*b^2) / (2-a-b))^2) - 1 +
      2*((b-a) / (2-a-b))) /
      ((((b-a) / (2-a-b))^2 + (Real.sqrt (4-2*a^2-2*b^2) / (2-a-b))^2) + 1) = b := by
  rw [squareChart_inverse_norm a b hD hrad]
  have hden : (2+a+b)/(2-a-b) + 1 = 4/(2-a-b) := by
    field_simp
    ring
  rw [hden]
  field_simp
  ring

end Markov
