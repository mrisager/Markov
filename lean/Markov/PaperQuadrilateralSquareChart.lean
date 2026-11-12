import Markov.SquareChartAlgebra

noncomputable section
namespace Markov

/-- The closed coordinate square with its four corners removed. -/
def paperPuncturedSquare : Set (ℝ × ℝ) :=
  {p | |p.1| ≤ 1 ∧ |p.2| ≤ 1 ∧ p.1 ^ 2 + p.2 ^ 2 < 2}

/-- The four corners of the closed coordinate square. -/
def paperSquareCorners : Set (ℝ × ℝ) :=
  {(-1, -1), (-1, 1), (1, -1), (1, 1)}

lemma paperSquare_coord_sq_le_one {a : ℝ} (ha : |a| ≤ 1) : a ^ 2 ≤ 1 := by
  rcases abs_le.mp ha with ⟨ha₁, ha₂⟩
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - a) (by linarith : 0 ≤ 1 + a)]

/-- The strict quadratic condition removes exactly the four corners. -/
theorem paperPuncturedSquare_eq_square_diff_corners :
    paperPuncturedSquare = {p : ℝ × ℝ | |p.1| ≤ 1 ∧ |p.2| ≤ 1} \ paperSquareCorners := by
  ext p
  rcases p with ⟨a, b⟩
  simp only [paperPuncturedSquare, paperSquareCorners, Set.mem_setOf_eq,
    Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨ha, hb, hlt⟩
    refine ⟨⟨ha, hb⟩, ?_⟩
    intro hc
    rcases hc with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;> norm_num at hlt
  · rintro ⟨⟨ha, hb⟩, hc⟩
    refine ⟨ha, hb, ?_⟩
    have ha₂ := paperSquare_coord_sq_le_one ha
    have hb₂ := paperSquare_coord_sq_le_one hb
    by_contra hn
    have hae : a ^ 2 = 1 := by nlinarith
    have hbe : b ^ 2 = 1 := by nlinarith
    have ha' : a = -1 ∨ a = 1 := by
      have : a ^ 2 = (1 : ℝ) ^ 2 := by simpa using hae
      rcases (sq_eq_sq_iff_eq_or_eq_neg).mp this with h | h
      · exact Or.inr h
      · exact Or.inl h
    have hb' : b = -1 ∨ b = 1 := by
      have : b ^ 2 = (1 : ℝ) ^ 2 := by simpa using hbe
      rcases (sq_eq_sq_iff_eq_or_eq_neg).mp this with h | h
      · exact Or.inr h
      · exact Or.inl h
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> simp at hc

/-- Positive denominator in the inverse square chart. -/
theorem paperPuncturedSquare_den_pos (p : paperPuncturedSquare) :
    0 < 2 - p.1.1 - p.1.2 := by
  rcases abs_le.mp p.2.1 with ⟨_, ha⟩
  rcases abs_le.mp p.2.2.1 with ⟨_, hb⟩
  have hs := p.2.2.2
  have hle : p.1.1 + p.1.2 ≤ 2 := by linarith
  have hne : p.1.1 + p.1.2 ≠ 2 := by
    intro h
    have ha' : p.1.1 = 1 := by linarith
    have hb' : p.1.2 = 1 := by linarith
    rw [ha', hb'] at hs
    norm_num at hs
  linarith [lt_of_le_of_ne hle hne]

/-- Positive radicand in the inverse square chart. -/
theorem paperPuncturedSquare_rad_pos (p : paperPuncturedSquare) :
    0 < 4 - 2 * p.1.1 ^ 2 - 2 * p.1.2 ^ 2 := by
  linarith [p.2.2.2]

/-- First coordinate of the explicit square chart. -/
def paperSquareChartA (z : UpperHalfPlane) : ℝ :=
  (Complex.normSq (z : ℂ) - 1 - 2 * z.re) / (Complex.normSq (z : ℂ) + 1)

/-- Second coordinate of the explicit square chart. -/
def paperSquareChartB (z : UpperHalfPlane) : ℝ :=
  (Complex.normSq (z : ℂ) - 1 + 2 * z.re) / (Complex.normSq (z : ℂ) + 1)

/-- The forward chart respects the exact circular and vertical side inequalities. -/
theorem paperSquareChart_mem (z : paperIdealQuadrilateral) :
    (paperSquareChartA z.1, paperSquareChartB z.1) ∈ paperPuncturedSquare := by
  have hz := (paperIdealQuadrilateral_mem_iff_abs_re z.1).mp z.2
  rcases abs_le.mp hz.1 with ⟨hx₁, hx₂⟩
  rcases abs_le.mp hz.2 with ⟨hN₁, hN₂⟩
  have hD : 0 < Complex.normSq (z.1 : ℂ) + 1 := by linarith [z.1.normSq_pos]
  change |(_ - 1 - 2 * _) / _| ≤ 1 ∧ |(_ - 1 + 2 * _) / _| ≤ 1 ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_le]
    constructor
    · rw [le_div_iff₀ hD]
      linarith
    · rw [div_le_iff₀ hD]
      linarith
  · rw [abs_le]
    constructor
    · rw [le_div_iff₀ hD]
      linarith
    · rw [div_le_iff₀ hD]
      linarith
  · change ((_ - 1 - 2 * _) / _) ^ 2 + ((_ - 1 + 2 * _) / _) ^ 2 < 2
    rw [div_pow, div_pow, ← add_div, div_lt_iff₀ (sq_pos_of_pos hD)]
    have hy := sq_pos_of_pos z.1.im_pos
    simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at *
    nlinarith

/-- Literal forward coordinate map on the actual paper quadrilateral. -/
def paperQuadrilateralToSquare (z : paperIdealQuadrilateral) : paperPuncturedSquare :=
  ⟨(paperSquareChartA z.1, paperSquareChartB z.1), paperSquareChart_mem z⟩

/-- Real coordinate of the inverse square chart. -/
def paperSquareInverseX (p : paperPuncturedSquare) : ℝ :=
  (p.1.2 - p.1.1) / (2 - p.1.1 - p.1.2)

/-- Positive imaginary coordinate of the inverse square chart. -/
def paperSquareInverseY (p : paperPuncturedSquare) : ℝ :=
  Real.sqrt (4 - 2 * p.1.1 ^ 2 - 2 * p.1.2 ^ 2) / (2 - p.1.1 - p.1.2)

theorem paperSquareInverseY_pos (p : paperPuncturedSquare) : 0 < paperSquareInverseY p := by
  exact div_pos (Real.sqrt_pos.2 (paperPuncturedSquare_rad_pos p))
    (paperPuncturedSquare_den_pos p)

/-- Literal inverse point in the upper half plane. -/
def paperSquareInversePoint (p : paperPuncturedSquare) : UpperHalfPlane :=
  ⟨⟨paperSquareInverseX p, paperSquareInverseY p⟩, paperSquareInverseY_pos p⟩

/-- Exact squared norm of the literal inverse point. -/
theorem paperSquareInversePoint_normSq (p : paperPuncturedSquare) :
    Complex.normSq (paperSquareInversePoint p : ℂ) =
      (2 + p.1.1 + p.1.2) / (2 - p.1.1 - p.1.2) := by
  simpa only [paperSquareInversePoint, Complex.normSq_apply, paperSquareInverseX,
    paperSquareInverseY, pow_two] using
      squareChart_inverse_norm _ _ (ne_of_gt (paperPuncturedSquare_den_pos p))
        (paperPuncturedSquare_rad_pos p).le

/-- The literal inverse point satisfies all four actual quadrilateral inequalities. -/
theorem paperSquareInversePoint_mem (p : paperPuncturedSquare) :
    paperSquareInversePoint p ∈ paperIdealQuadrilateral := by
  rw [paperIdealQuadrilateral_mem_iff_abs_re]
  have hD := paperPuncturedSquare_den_pos p
  rcases abs_le.mp p.2.1 with ⟨ha₁, ha₂⟩
  rcases abs_le.mp p.2.2.1 with ⟨hb₁, hb₂⟩
  change |paperSquareInverseX p| ≤ 1 ∧
    |paperSquareInverseX p| ≤ Complex.normSq (paperSquareInversePoint p : ℂ)
  rw [paperSquareInversePoint_normSq]
  dsimp only [paperSquareInverseX]
  constructor
  · rw [abs_le]
    constructor
    · rw [le_div_iff₀ hD]
      linarith
    · rw [div_le_iff₀ hD]
      linarith
  · rw [abs_le, ← neg_div, div_le_div_iff_of_pos_right hD, div_le_div_iff_of_pos_right hD]
    constructor <;> linarith

/-- Literal inverse coordinate map to the actual quadrilateral. -/
def paperSquareToQuadrilateral (p : paperPuncturedSquare) : paperIdealQuadrilateral :=
  ⟨paperSquareInversePoint p, paperSquareInversePoint_mem p⟩

/-- The inverse chart recovers every actual upper-half-plane point. -/
theorem paperSquareToQuadrilateral_leftInverse :
    Function.LeftInverse paperSquareToQuadrilateral paperQuadrilateralToSquare := by
  intro z
  apply Subtype.ext
  apply UpperHalfPlane.ext_re_im
  · simpa only [paperSquareToQuadrilateral, paperSquareInversePoint, paperSquareInverseX,
      paperQuadrilateralToSquare, paperSquareChartA, paperSquareChartB,
      UpperHalfPlane.re, Complex.normSq_apply, UpperHalfPlane.coe_im, pow_two] using
        squareChart_forward_inverse_x z.1.re z.1.im
  · simpa only [paperSquareToQuadrilateral, paperSquareInversePoint, paperSquareInverseY,
      paperQuadrilateralToSquare, paperSquareChartA, paperSquareChartB,
      UpperHalfPlane.im, Complex.normSq_apply, UpperHalfPlane.coe_re, pow_two] using
        squareChart_forward_inverse_y z.1.re z.1.im z.1.im_pos

/-- The forward chart recovers every corner-removed square point. -/
theorem paperQuadrilateralToSquare_leftInverse :
    Function.LeftInverse paperQuadrilateralToSquare paperSquareToQuadrilateral := by
  intro p
  apply Subtype.ext
  apply Prod.ext
  · simpa only [paperQuadrilateralToSquare, paperSquareToQuadrilateral,
      paperSquareChartA, paperSquareInversePoint, Complex.normSq_apply,
      paperSquareInverseX, paperSquareInverseY, UpperHalfPlane.re, pow_two] using
      squareChart_inverse_forward_a p.1.1 p.1.2
        (ne_of_gt (paperPuncturedSquare_den_pos p)) (paperPuncturedSquare_rad_pos p).le
  · simpa only [paperQuadrilateralToSquare, paperSquareToQuadrilateral,
      paperSquareChartB, paperSquareInversePoint, Complex.normSq_apply,
      paperSquareInverseX, paperSquareInverseY, UpperHalfPlane.re, pow_two] using
      squareChart_inverse_forward_b p.1.1 p.1.2
        (ne_of_gt (paperPuncturedSquare_den_pos p)) (paperPuncturedSquare_rad_pos p).le

/-- Continuity of the first rational coordinate. -/
theorem continuous_paperSquareChartA : Continuous paperSquareChartA := by
  unfold paperSquareChartA
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    exact ne_of_gt (by linarith [z.normSq_pos])

/-- Continuity of the second rational coordinate. -/
theorem continuous_paperSquareChartB : Continuous paperSquareChartB := by
  unfold paperSquareChartB
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    exact ne_of_gt (by linarith [z.normSq_pos])

/-- Continuity of the literal forward chart. -/
theorem continuous_paperQuadrilateralToSquare : Continuous paperQuadrilateralToSquare := by
  apply Continuous.subtype_mk
  exact (continuous_paperSquareChartA.comp continuous_subtype_val).prodMk
    (continuous_paperSquareChartB.comp continuous_subtype_val)

/-- Continuity of the inverse real coordinate. -/
theorem continuous_paperSquareInverseX : Continuous paperSquareInverseX := by
  unfold paperSquareInverseX
  apply Continuous.div
  · fun_prop
  · fun_prop
  · exact fun p => ne_of_gt (paperPuncturedSquare_den_pos p)

/-- Continuity of the inverse imaginary coordinate. -/
theorem continuous_paperSquareInverseY : Continuous paperSquareInverseY := by
  unfold paperSquareInverseY
  apply Continuous.div
  · fun_prop
  · fun_prop
  · exact fun p => ne_of_gt (paperPuncturedSquare_den_pos p)

/-- Continuity of the literal inverse point. -/
theorem continuous_paperSquareInversePoint : Continuous paperSquareInversePoint := by
  apply Continuous.upperHalfPlaneMk
  exact Complex.equivRealProdCLM.symm.continuous.comp
    (continuous_paperSquareInverseX.prodMk continuous_paperSquareInverseY)

/-- Continuity of the literal inverse chart. -/
theorem continuous_paperSquareToQuadrilateral : Continuous paperSquareToQuadrilateral := by
  exact continuous_paperSquareInversePoint.subtype_mk _

/-- Explicit homeomorphism from the actual paper ideal quadrilateral to the
closed square with its four corners removed. -/
def paperQuadrilateralSquareHomeomorph : paperIdealQuadrilateral ≃ₜ paperPuncturedSquare where
  toFun := paperQuadrilateralToSquare
  invFun := paperSquareToQuadrilateral
  left_inv := paperSquareToQuadrilateral_leftInverse
  right_inv := paperQuadrilateralToSquare_leftInverse
  continuous_toFun := continuous_paperQuadrilateralToSquare
  continuous_invFun := continuous_paperSquareToQuadrilateral

end Markov
