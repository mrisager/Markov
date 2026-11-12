import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Parameter changes used when passing from the paper's real cutoff to
the natural cutoff at its floor. The common decay rate is the minimum of
the diameter and corner rates. The loss in the arc denominator is at most
four, uniformly for real heights at least one. -/

namespace Markov

/-- A single positive rate can be used for both diameter and corner decay. -/
theorem cutoff_common_rate_pos (cD K : ℝ) (hcD : 0 < cD) (hK : 0 < K) :
    0 < min cD K := lt_min hcD hK

/-- The paper's quotient bound on the angular error implies the bound
with coefficient `m / 2` and the common diameter/corner decay rate. -/
theorem cutoff_eta_le_common_rate
    (m ε cD K H η : ℝ) (hm : 0 < m) (hε : 0 < ε) (hH : 0 ≤ H)
    (hη : η ≤ (m / (2 + ε)) * Real.exp (-K * H)) :
    η ≤ (m / 2) * Real.exp (-(min cD K) * H) := by
  have hcoeff : m / (2 + ε) ≤ m / 2 := by
    apply (div_le_iff₀ (show 0 < 2 + ε by linarith)).2
    nlinarith
  have hexp : Real.exp (-K * H) ≤ Real.exp (-(min cD K) * H) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_right cD K) hH
    linarith
  exact hη.trans (mul_le_mul hcoeff hexp (Real.exp_pos _).le (by positivity))

/-- The original displayed basic assumption gives the quotient bound. -/
theorem cutoff_eta_le_of_basic_assumption
    (m ε K H η : ℝ) (hε : 0 < ε)
    (hη : (2 + ε) * η ≤ m * Real.exp (-K * H)) :
    η ≤ (m / (2 + ε)) * Real.exp (-K * H) := by
  have hden : 0 < 2 + ε := by linarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).2
  simpa only [mul_comm] using hη

/-- The basic assumption in its paper form controls the angular error at
the common rate. -/
theorem cutoff_eta_le_common_rate_of_basic_assumption
    (m ε cD K H η : ℝ) (hm : 0 < m) (hε : 0 < ε) (hH : 0 ≤ H)
    (hη : (2 + ε) * η ≤ m * Real.exp (-K * H)) :
    η ≤ (m / 2) * Real.exp (-(min cD K) * H) := by
  exact cutoff_eta_le_common_rate m ε cD K H η hm hε hH
    (cutoff_eta_le_of_basic_assumption m ε K H η hε hη)

/-- The natural cutoff at the floor is positive and differs from a real
height at least one by at most a factor of two. -/
theorem cutoff_natFloor_bounds (H : ℝ) (hH : 1 ≤ H) :
    1 ≤ ⌊H⌋₊ ∧ (⌊H⌋₊ : ℝ) ≤ H ∧ H ≤ 2 * (⌊H⌋₊ : ℝ) := by
  have hn : 1 ≤ ⌊H⌋₊ := Nat.floor_pos.mpr hH
  have hnR : (1 : ℝ) ≤ (⌊H⌋₊ : ℝ) := by exact_mod_cast hn
  have hlt := Nat.lt_floor_add_one H
  exact ⟨hn, Nat.floor_le (by linarith), by linarith⟩

/-- The common-rate angular error bound also holds at the natural floor. -/
theorem cutoff_eta_le_common_rate_natFloor
    (m ε cD K H η : ℝ) (hm : 0 < m) (hε : 0 < ε)
    (hcD : 0 < cD) (hK : 0 < K) (hH : 1 ≤ H)
    (hη : η ≤ (m / (2 + ε)) * Real.exp (-K * H)) :
    η ≤ (m / 2) * Real.exp (-(min cD K) * (⌊H⌋₊ : ℝ)) := by
  have hreal := cutoff_eta_le_common_rate m ε cD K H η hm hε (by linarith) hη
  apply hreal.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hfloor := (cutoff_natFloor_bounds H hH).2.1
  have hc := (cutoff_common_rate_pos cD K hcD hK).le
  nlinarith

/-- The paper form of the basic assumption controls the error at the
natural floor using the common positive rate. -/
theorem cutoff_eta_le_common_rate_natFloor_of_basic_assumption
    (m ε cD K H η : ℝ) (hm : 0 < m) (hε : 0 < ε)
    (hcD : 0 < cD) (hK : 0 < K) (hH : 1 ≤ H)
    (hη : (2 + ε) * η ≤ m * Real.exp (-K * H)) :
    η ≤ (m / 2) * Real.exp (-(min cD K) * (⌊H⌋₊ : ℝ)) := by
  exact cutoff_eta_le_common_rate_natFloor m ε cD K H η hm hε hcD hK hH
    (cutoff_eta_le_of_basic_assumption m ε K H η hε hη)

/-- An upper bound on the natural cutoff gives the real-height bound
with at most twice the constant. -/
theorem cutoff_real_height_le_of_natFloor_le
    (H L D A : ℝ) (hH : 1 ≤ H)
    (hbound : (⌊H⌋₊ : ℝ) ≤ L * D * A ^ 2) :
    H ≤ (2 * L) * D * A ^ 2 := by
  have hfloor := (cutoff_natFloor_bounds H hH).2.2
  nlinarith

/-- The square-root factor incurs at most a factor of two on passing
from the natural floor to the real height. -/
theorem cutoff_sqrt_le_twice_natFloor_sqrt (H : ℝ) (hH : 1 ≤ H) :
    Real.sqrt H ≤ 2 * Real.sqrt (⌊H⌋₊ : ℝ) := by
  have hfloor := (cutoff_natFloor_bounds H hH).2.2
  have hn0 : (0 : ℝ) ≤ (⌊H⌋₊ : ℝ) := Nat.cast_nonneg _
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hn0]

/-- The denominator at the real height lies between the floor denominator
and four times that denominator. -/
theorem cutoff_sqrt_denominator_bounds (H : ℝ) (hH : 1 ≤ H) :
    (⌊H⌋₊ : ℝ) * Real.sqrt (⌊H⌋₊ : ℝ) ≤ H * Real.sqrt H ∧
    H * Real.sqrt H ≤ 4 * ((⌊H⌋₊ : ℝ) * Real.sqrt (⌊H⌋₊ : ℝ)) := by
  obtain ⟨_, hfloor, htwice⟩ := cutoff_natFloor_bounds H hH
  constructor
  · exact mul_le_mul hfloor (Real.sqrt_le_sqrt hfloor)
      (Real.sqrt_nonneg _) (by linarith)
  · calc
      H * Real.sqrt H ≤
          (2 * (⌊H⌋₊ : ℝ)) * (2 * Real.sqrt (⌊H⌋₊ : ℝ)) :=
        mul_le_mul htwice (cutoff_sqrt_le_twice_natFloor_sqrt H hH)
          (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring

/-- A reciprocal floor denominator is bounded by four times the real
height denominator. -/
theorem cutoff_natFloor_reciprocal_le (H : ℝ) (hH : 1 ≤ H) :
    1 / ((⌊H⌋₊ : ℝ) * Real.sqrt (⌊H⌋₊ : ℝ)) ≤
      4 / (H * Real.sqrt H) := by
  have hn : (0 : ℝ) < (⌊H⌋₊ : ℝ) := by
    have := (cutoff_natFloor_bounds H hH).1
    exact_mod_cast (show 0 < ⌊H⌋₊ by omega)
  have hH0 : 0 < H := by linarith
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  simpa only [one_mul] using (cutoff_sqrt_denominator_bounds H hH).2

/-- Multiplying the reciprocal comparison by any nonnegative numerator
gives the denominator conversion used for arc estimates. -/
theorem cutoff_natFloor_quotient_le (H C : ℝ) (hH : 1 ≤ H) (hC : 0 ≤ C) :
    C / ((⌊H⌋₊ : ℝ) * Real.sqrt (⌊H⌋₊ : ℝ)) ≤
      (4 * C) / (H * Real.sqrt H) := by
  have h := mul_le_mul_of_nonneg_left (cutoff_natFloor_reciprocal_le H hH) hC
  convert h using 1 <;> ring

/-- An arc bound at the natural floor transfers to the real cutoff with
at most a factor of four in its numerator. -/
theorem cutoff_arc_bound_of_natFloor_bound
    (H C s : ℝ) (hH : 1 ≤ H) (hC : 0 ≤ C)
    (hbound : s ≤ C / ((⌊H⌋₊ : ℝ) * Real.sqrt (⌊H⌋₊ : ℝ))) :
    s ≤ (4 * C) / (H * Real.sqrt H) :=
  hbound.trans (cutoff_natFloor_quotient_le H C hH hC)

end Markov
