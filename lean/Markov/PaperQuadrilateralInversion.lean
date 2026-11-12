import Markov.ModularPolygonSides
import Markov.ModularClosedAdmissibility

/-! Exact coordinate characterization and inversion symmetry of the paper's
actual ideal quadrilateral. No fundamental-domain assertion is used. -/

noncomputable section
open scoped MatrixGroups
namespace Markov

/-- The two circular inequalities are equivalent to the absolute real-coordinate
bound by the squared complex norm. -/
theorem paperIdealQuadrilateral_mem_iff_abs_re (z : UpperHalfPlane) :
    z ∈ paperIdealQuadrilateral ↔
      |z.re| ≤ 1 ∧ |z.re| ≤ Complex.normSq (z : ℂ) := by
  change (-1 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.re ^ 2 + z.re + z.im ^ 2 ∧
    0 ≤ z.re ^ 2 - z.re + z.im ^ 2) ↔ _
  simp only [abs_le, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  constructor
  · intro hz
    exact ⟨⟨hz.1, hz.2.1⟩,
      ⟨by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩⟩
  · rintro ⟨hr, hn⟩
    exact ⟨hr.1, hr.2, by linarith [hn.1], by linarith [hn.2]⟩

/-- The exact real coordinate of the actual modular inversion. -/
theorem modular_S_re_div_normSq (z : UpperHalfPlane) :
    (ModularGroup.S • z).re = -z.re / Complex.normSq (z : ℂ) := by
  rw [UpperHalfPlane.modular_S_smul]
  change Complex.re ((-(z : ℂ))⁻¹) = _
  rw [Complex.inv_re, Complex.neg_re, Complex.normSq_neg]
  rfl

/-- Actual modular inversion interchanges the vertical and circular
inequalities and preserves the paper quadrilateral exactly. -/
theorem paperIdealQuadrilateral_S_mem_iff (z : UpperHalfPlane) :
    ModularGroup.S • z ∈ paperIdealQuadrilateral ↔ z ∈ paperIdealQuadrilateral := by
  rw [paperIdealQuadrilateral_mem_iff_abs_re, paperIdealQuadrilateral_mem_iff_abs_re,
    modular_S_re_div_normSq, modular_normSq_S_smul]
  simp only [abs_div, abs_neg, abs_of_pos z.normSq_pos]
  rw [div_le_iff₀ z.normSq_pos, div_le_iff₀ z.normSq_pos]
  simp only [one_mul, inv_mul_cancel₀ z.normSq_ne_zero]
  exact and_comm

/-- The actual quadrilateral is closed in the upper-half-plane topology. -/
theorem paperIdealQuadrilateral_isClosed : IsClosed paperIdealQuadrilateral := by
  have hset : paperIdealQuadrilateral =
      {z : UpperHalfPlane | |z.re| ≤ 1 ∧ |z.re| ≤ Complex.normSq (z : ℂ)} := by
    ext z
    exact paperIdealQuadrilateral_mem_iff_abs_re z
  rw [hset]
  have h1 : IsClosed {z : UpperHalfPlane | |z.re| ≤ 1} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have h2 : IsClosed {z : UpperHalfPlane | |z.re| ≤ Complex.normSq (z : ℂ)} :=
    isClosed_le (by fun_prop) (by fun_prop)
  exact h1.inter h2

end Markov
