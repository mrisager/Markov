import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! The exact signed turn of three normalized planar rays. This algebraic
lemma identifies the local convexity condition for a polygonal Farey fan;
it assumes no norm or global convexity theorem. -/

noncomputable section

namespace Markov

/-- Oriented determinant of two real coordinate vectors. -/
def realDet (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- A direction scaled by a prescribed nonzero candidate length. -/
def normalizedRay (u : ℝ × ℝ) (L : ℝ) : ℝ × ℝ := (u.1 / L, u.2 / L)

/-- The determinant of the two outer directions records the integer-fan
coefficient in their sum. This statement is valid for a real coefficient. -/
theorem realDet_outer_eq (v u w : ℝ × ℝ) (k : ℝ)
    (hvu : realDet v u = 1) (hsum : v + w = k • u) : realDet v w = k := by
  calc
    realDet v w = realDet v (v + w) := by simp [realDet]; ring
    _ = realDet v (k • u) := by rw [hsum]
    _ = k * realDet v u := by simp [realDet]; ring
    _ = k := by rw [hvu, mul_one]

/-- The exact local turn of the normalized polygon. All dependence on the
candidate lengths is in the one scalar corner inequality. -/
theorem normalized_fan_turn_identity (v u w : ℝ × ℝ) (k Lv Lu Lw : ℝ)
    (hvu : realDet v u = 1) (huw : realDet u w = 1)
    (hsum : v + w = k • u) (hLv : Lv ≠ 0) (hLu : Lu ≠ 0) (hLw : Lw ≠ 0) :
    realDet (normalizedRay u Lu - normalizedRay v Lv)
      (normalizedRay w Lw - normalizedRay u Lu) =
        (Lv + Lw - k * Lu) / (Lv * Lu * Lw) := by
  have hvw := realDet_outer_eq v u w k hvu hsum
  simp only [realDet, normalizedRay, Prod.fst_sub, Prod.snd_sub] at *
  field_simp
  linear_combination Lv * Lu * huw + Lw * Lu * hvu - Lu ^ 2 * hvw

/-- Strict corner inequality is exactly a positive normalized polygon turn. -/
theorem normalized_fan_turn_pos_iff (v u w : ℝ × ℝ) (k Lv Lu Lw : ℝ)
    (hvu : realDet v u = 1) (huw : realDet u w = 1)
    (hsum : v + w = k • u) (hLv : 0 < Lv) (hLu : 0 < Lu) (hLw : 0 < Lw) :
    0 < realDet (normalizedRay u Lu - normalizedRay v Lv)
      (normalizedRay w Lw - normalizedRay u Lu) ↔ k * Lu < Lv + Lw := by
  rw [normalized_fan_turn_identity v u w k Lv Lu Lw hvu huw hsum hLv.ne' hLu.ne' hLw.ne']
  have hden : 0 < Lv * Lu * Lw := by positivity
  rw [lt_div_iff₀ hden, zero_mul, sub_pos]

/-- The nonstrict local convexity criterion. -/
theorem normalized_fan_turn_nonneg_iff (v u w : ℝ × ℝ) (k Lv Lu Lw : ℝ)
    (hvu : realDet v u = 1) (huw : realDet u w = 1)
    (hsum : v + w = k • u) (hLv : 0 < Lv) (hLu : 0 < Lu) (hLw : 0 < Lw) :
    0 ≤ realDet (normalizedRay u Lu - normalizedRay v Lv)
      (normalizedRay w Lw - normalizedRay u Lu) ↔ k * Lu ≤ Lv + Lw := by
  rw [normalized_fan_turn_identity v u w k Lv Lu Lw hvu huw hsum hLv.ne' hLu.ne' hLw.ne']
  have hden : 0 < Lv * Lu * Lw := by positivity
  rw [le_div_iff₀ hden, zero_mul, sub_nonneg]

/-- The strict corner inequality supplies a positive polygonal turn. -/
theorem normalized_fan_turn_pos (v u w : ℝ × ℝ) (k Lv Lu Lw : ℝ)
    (hvu : realDet v u = 1) (huw : realDet u w = 1)
    (hsum : v + w = k • u) (hLv : 0 < Lv) (hLu : 0 < Lu) (hLw : 0 < Lw)
    (hcorner : k * Lu < Lv + Lw) :
    0 < realDet (normalizedRay u Lu - normalizedRay v Lv)
      (normalizedRay w Lw - normalizedRay u Lu) :=
  (normalized_fan_turn_pos_iff v u w k Lv Lu Lw hvu huw hsum hLv hLu hLw).mpr hcorner

end Markov
