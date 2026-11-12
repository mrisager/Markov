import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Algebraic identities from Section 2 and Proposition 4. -/

namespace Markov

def Fricke (a b c : ℝ) : Prop := a ^ 2 + b ^ 2 + c ^ 2 = a * b * c

theorem normalized_fricke (a b c : ℝ) (h : Fricke a b c) :
    (a / 3) ^ 2 + (b / 3) ^ 2 + (c / 3) ^ 2 =
      3 * (a / 3) * (b / 3) * (c / 3) := by
  dsimp [Fricke] at h
  nlinarith [h]

theorem vieta_preserves_equation (p q r : ℤ)
    (h : p ^ 2 + q ^ 2 + r ^ 2 = 3 * p * q * r) :
    p ^ 2 + q ^ 2 + (3 * p * q - r) ^ 2 = 3 * p * q * (3 * p * q - r) := by
  nlinarith [h]

theorem fricke_opposite_product (a b c : ℝ) (h : Fricke a b c) :
    c * (a * b - c) = a ^ 2 + b ^ 2 := by
  dsimp [Fricke] at h
  nlinarith [h]

/-- The algebraic calculation in Proposition 4(iii). -/
theorem quadratic_trace_identity (r b c : ℝ) (hr : r - r⁻¹ ≠ 0) :
    (c - r⁻¹ * b) / (r - r⁻¹) +
      (r * b - c) / (r - r⁻¹) = b := by
  rw [← add_div, div_eq_iff hr]
  ring

/-- The algebraic calculation in Proposition 4(ii), with `a = r + r⁻¹`. -/
theorem quadratic_norm_identity (r a b c : ℝ) (hr : r ≠ 0)
    (ha : a = r + r⁻¹) (hf : Fricke a b c) :
    ((c - r⁻¹ * b) / (r - r⁻¹)) *
      ((r * b - c) / (r - r⁻¹)) = a ^ 2 / (a ^ 2 - 4) := by
  have hd : (r - r⁻¹) ^ 2 = a ^ 2 - 4 := by
    rw [ha]
    field_simp [hr]
    ring
  rw [← hd]
  have hn : (c - r⁻¹ * b) * (r * b - c) = a ^ 2 := by
    dsimp [Fricke] at hf
    have hinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
    calc
      _ = (r + r⁻¹) * b * c - c ^ 2 - (r * r⁻¹) * b ^ 2 := by ring
      _ = a * b * c - c ^ 2 - b ^ 2 := by rw [← ha, hinv]; ring
      _ = a ^ 2 := by linarith
  rw [div_mul_div_comm, ← pow_two, hn]

/-- The monic-polynomial identity used for Proposition 4(iv). -/
theorem scaled_root_identity (A B Δ a b : ℝ)
    (hsum : A + B = b) (hprod : Δ * (A * B) = a ^ 2) :
    (Δ * A) ^ 2 - Δ * b * (Δ * A) + Δ * a ^ 2 = 0 := by
  rw [← hsum, ← hprod]
  ring

end Markov
